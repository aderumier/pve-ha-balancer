#!/usr/bin/perl

use strict;
use warnings;
use PVE::API2Tools;
use PVE::Cluster qw(cfs_read_file);
use PVE::INotify;
use PVE::Exception qw(raise raise_perm_exc raise_param_exc);
use PVE::RESTHandler;
use PVE::RPCEnvironment;
use PVE::JSONSchema qw(get_standard_option);
use PVE::LXC;
use PVE::HA::Env::PVE2;
use PVE::HA::Config;
use PVE::QemuConfig;
use PVE::LXC::Config;
use PVE::QemuServer;
use Data::Dumper;

PVE::RPCEnvironment->setup_default_cli_env();

my $mem_threshold = 10;
my $cpu_threshold = 10;
my $nodename = PVE::INotify::nodename();

while(1) {
    print "reduce node load\n";
    reduce_node_load($nodename,$mem_threshold, $cpu_threshold);
    sleep 15;
}

sub reduce_node_load {
    my ($nodename, $mem_threshold, $cpu_threshold) = @_;
    #reduce load under defined threshold
    PVE::Cluster::cfs_update();
    PVE::Cluster::check_cfs_quorum();

    my $rpcenv = PVE::RPCEnvironment::get();
    my $authuser = $rpcenv->get_user();
    $rpcenv->{type} = 'priv'; # to start tasks in background
    my $storecfg = PVE::Storage::config();

    my $target_mem_threshold = $mem_threshold - 10; #lower a little bit the target, to avoid infinite migration loop
    my $target_cpu_threshold = $cpu_threshold - 10;

    my ($node_mem_pct, $node_cpu_pct) = get_node_stats($nodename);
    if ($node_mem_pct < $mem_threshold && $node_cpu_pct < $cpu_threshold) {
	print"node threshold are ok. Nothing to do\n";
    } else {
	print"node threshold are too high. Looking for vm to migrate\n";
    }

    my ($vmlist_ordered, $vmlist) = get_vm_ordered_list($nodename, $mem_threshold, $cpu_threshold, $node_mem_pct, $node_cpu_pct);

    my ($vmid, $target) = find_best_vm_target($nodename, $vmlist, $vmlist_ordered, $storecfg, $target_mem_threshold, $target_cpu_threshold);
    if (!$vmid && !$target) {
	print "can't find any vm to migrate to reduce load\n";
	return;
    }

    migrate_vm($nodename, $vmid, $target, $vmlist);
};

sub dotprod {
    my($vec_a, $vec_b, $mode) = @_;
    die "they must have the same size\n" unless @$vec_a == @$vec_b;
    $mode = "" if !$mode;
    my $sum = 0;
    my $norm_a = 0;
    my $norm_b = 0;

    for(my $i=0; $i < scalar @{$vec_a}; $i++) {
	my $a = @{$vec_a}[$i];
	my $b = @{$vec_b}[$i];

	$sum += $a * $b;
	$norm_a += $a * $a;
	$norm_b += $b * $b;
    }

    if($mode eq 'normR') {
	return $sum / (sqrt($norm_a) * sqrt($norm_b))
    } elsif ($mode eq 'normC') {
	return $sum / $norm_b;
    }
    return $sum;
}

sub find_best_node_target {
    my($vmid, $d, $nodename, $storecfg, $mem_threshold, $cpu_threshold, $hagroup) = @_;

    my $vmconf = $d->{conf};
    my $members = PVE::Cluster::get_members();
    my $rrd = PVE::Cluster::rrd_dump();

    my $nodelist;
    my $current_prio = 1;

    if($hagroup) {
	my $nodesprio = $hagroup->{nodes};
	my $prio_group;
	foreach my $nodeprio (keys %{$nodesprio}) {
	    my ($node, $prio) = split(':', $nodeprio);
	    $nodelist->{$node} = $prio;
	    push @{$prio_group->{$prio}}, $node;
	}
	$current_prio = $nodelist->{$nodename};

    } else {
	my $nodelist_array = PVE::Cluster::get_nodelist();
	foreach my $node (@$nodelist_array) {
	    $nodelist->{$node} = 1; 
	}
    }
    

    $mem_threshold = 0.8 if !$mem_threshold;
    $cpu_threshold = 0.8 if !$cpu_threshold;

    my ($vm_cpu, $vm_mem, $vm_maxcpu, $vm_maxmem) = get_vm_rrd_stats($vmid, 80);
    my @vec_vm = ($vm_cpu, $vm_mem);  #? add network usage dimension ?

    my $nodes_order = {};
    foreach my $node (keys %$nodelist) {
	next if $node eq $nodename;

	#skip if target prio < current prio && !nofailback (avoid failback after migration)
	next if $hagroup && !$hagroup->{nofailback} && $nodelist->{$node} < $current_prio;

	next if check_hagroup_antiaffinity($node, $hagroup);

	my $node_stats = PVE::API2Tools::extract_node_stats($node, $members, $rrd);
	next if $node_stats->{status} ne 'online';

	#check if target node have enough cpu/mem ressources
	my $node_freemem = $node_stats->{maxmem} - $node_stats->{mem};
	my $node_freecpu = (100 - $node_stats->{cpu}) * $node_stats->{maxcpu};  #how to handle different cpu model power ? bogomips ?
	next if $node_freecpu * $cpu_threshold < $vm_cpu;
	next if $node_freemem * $mem_threshold < $vm_mem;
	next if $node_stats->{maxcpu} < $vm_maxcpu;
	next if $node_freemem < $vm_maxmem;

	if ($d->{type} eq 'qemu') {
	    eval { PVE::QemuServer::check_storage_availability($storecfg, $vmconf, $node) };
	    next if $@;
	}
	# fixme: check vmbr available

	#for target node ordering, use also swap && ksm;
	#$node_freemem = $node_freemem - $node_stats->{swapused} - $node_stats->{ksm_shared};

	my @vec_node = ($node_freecpu, $node_freemem); #? add network usage dimension ?
	my $weight = dotprod(\@vec_vm,\@vec_node);
	$nodes_order->{$node}->{weight} = $weight;
	$nodes_order->{$node}->{prio} = $nodelist->{$node};
    }
    my @target_array = sort { $a->{prio} <=> $b->{prio} || $a->{weight} <=> $b->{weight} } keys %$nodes_order;

    my $target = $target_array[0];

    if(!$target) {
	print "can't find any target node for vm $vmid\n";
	return;
    } else {
	print "best vm to migrate:$vmid best target:$target\n";
    }
    return $target;
}

sub get_vm_rrd_stats {
    my ($vmid, $percentile) = @_;

    my $rrdname = "pve2-vm/$vmid";
    my $rrddir = "/var/lib/rrdcached/db";

    my $rrd = "$rrddir/$rrdname";

    my ($reso, $count) = (1,60);

    my $ctime  = $reso*int(time()/$reso);
    my $req_start = $ctime - $reso*$count;

    my $cf = "AVERAGE";

    my @args = (
	"-s" => '-6m',
	"-r" => '1m',
	);

    my $socket = "/var/run/rrdcached.sock";
    push @args, "--daemon" => "unix:$socket" if -S $socket;

    my ($start, $step, $names, $data) = RRDs::fetch($rrd, $cf, @args);

    my @cpu = ();
    my @mem = ();
    my @maxmem = ();
    my @maxcpu = ();

    foreach my $rec (@$data) {
	my $maxcpu = @$rec[0] || 0;
	my $cpu = @$rec[1] || 0;
	my $maxmem = @$rec[2] || 0;
	my $mem = @$rec[3] || 0;
	push @cpu, $cpu*$maxcpu;
	push @mem, $mem;
	push @maxcpu, $maxcpu;
	push @maxmem, $maxmem;
    }

    my $cpu_percentile = percentile($percentile, \@cpu);
    my $mem_percentile = percentile($percentile, \@mem);
    my $maxmem_percentile = percentile($percentile, \@maxmem);
    my $maxcpu_percentile = percentile($percentile, \@maxcpu);
    return ($cpu_percentile, $mem_percentile, $maxcpu_percentile, $maxmem_percentile);
}

sub percentile {
    my ($p, $aref) = @_;
    my $percentile = int($p * $#{$aref}/100);
    return (sort @$aref)[$percentile];
}

sub get_vm_ordered_list {
    my ($nodename, $mem_threshold, $cpu_threshold, $node_mem_pct, $node_cpu_pct) = @_;

    my $rrd = PVE::Cluster::rrd_dump();

    my $vmlist = get_filtered_vmlist($nodename, undef, 0, 1);

    foreach my $vmid (sort keys %$vmlist) {
	my $d = $vmlist->{$vmid};
	my $vmconf = $d->{conf};
	my ($cpu, $mem, $maxcpu, $maxmem) = get_vm_rrd_stats($vmid, 80);
	$d->{cpu} = $cpu;
	$d->{mem} = $mem;
	$d->{maxcpu} = $mem;
	$d->{maxmem} = $maxmem;
	#skip locked vm
	delete $vmlist->{$vmid} if $vmconf->{lock};
	#skip vm if uptime < 5min
	my $vm_stats = PVE::API2Tools::extract_vm_stats($vmid, $d, $rrd);
	delete $vmlist->{$vmid} if $vm_stats->{uptime} < 300;
    }

    my $vmlist_ordered;
    #order vmlist with bigger usage to reduce number of vm migration
    if ($node_mem_pct < $mem_threshold && $node_cpu_pct < $cpu_threshold) {
	#order by cpu, then ram ?
	@{$vmlist_ordered} = sort { $vmlist->{$a}->{mem} <=> $vmlist->{$b}->{mem} || $vmlist->{$a}->{cpu} <=> $vmlist->{$b}->{cpu} } keys %$vmlist;
    } elsif ($node_mem_pct < $mem_threshold) {
	#order by mem usage first
	@{$vmlist_ordered} = sort { $vmlist->{$a}->{mem} <=> $vmlist->{$b}->{mem} } keys %$vmlist;
    } elsif ($node_cpu_pct < $cpu_threshold) {
	#order by cpu usage first
	@{$vmlist_ordered} = sort { $vmlist->{$a}->{cpu} <=> $vmlist->{$b}->{cpu} } keys %$vmlist;
    }

    return ($vmlist_ordered, $vmlist);
}

sub get_node_stats {
    my ($nodename) = @_;

    my $rrd = PVE::Cluster::rrd_dump();
    my $members = PVE::Cluster::get_members();
    my $node_stats = PVE::API2Tools::extract_node_stats($nodename, $members, $rrd);

    my $node_mem_pct = $node_stats->{mem} / $node_stats->{maxmem} * 100;
    my $node_cpu_pct = $node_stats->{cpu} / $node_stats->{maxcpu};
    return ($node_mem_pct, $node_cpu_pct);
}

sub find_best_vm_target {
    my ($nodename, $vmlist, $vmlist_ordered, $storecfg, $target_mem_threshold, $target_cpu_threshold) = @_;

    foreach my $vmid (@{$vmlist_ordered}) {
	print "try to find a target for vm $vmid\n";
	my $d = $vmlist->{$vmid};
	my $hagroup = undef;
	if(PVE::HA::Config::vm_is_ha_managed($vmid)) {
		my $groups = PVE::HA::Env::PVE2::read_group_config();
		my $sc = PVE::HA::Env::PVE2::read_service_config();
		my $group = $sc->{"vm:$vmid"}->{group};
		$hagroup = $groups->{ids}->{$group};
		$hagroup->{name} = $group;
	}

	my $target = find_best_node_target($vmid, $d, $nodename, $storecfg, $target_mem_threshold/100, $target_cpu_threshold/100, $hagroup);
	next if !$target;
	return ($vmid, $target);
   }

}


sub migrate_vm {
    my ($nodename, $vmid, $target, $vmlist) = @_;

    return if check_running_migrate_job();

    my $d = $vmlist->{$vmid};
    my $workers = {};
    my $maxWorkers = 1;

    my $pid;
    eval { $pid = create_migrate_worker($nodename, $d->{type}, $vmid, $target); };
    warn $@ if $@;
    next if !$pid;

    $workers->{$pid} = 1;
    while (scalar(keys %$workers) >= $maxWorkers) {
	foreach my $p (keys %$workers) {
	    if (!PVE::ProcFSTools::check_process_running($p)) {
		delete $workers->{$p};
	    }
	}
	sleep(1);
    }
}

sub check_running_migrate_job {

    PVE::Cluster::cfs_update();

    my $nodelist = PVE::Cluster::get_nodelist();
    foreach my $nodename (@$nodelist) {
	my $vmlist = get_filtered_vmlist($nodename,undef,undef,1);
	foreach my $vmid (sort keys %$vmlist) {
	    my $d = $vmlist->{$vmid};
	    if($d->{type} eq 'lxc') {
		if (PVE::LXC::Config->has_lock($d->{conf}, 'migrate')) {
		    print "migration job are already already running";
		    return 1;
		}

	    } elsif ($d->{type} eq 'qemu') {
		if (PVE::QemuConfig->has_lock($d->{conf}, 'migrate')) {
		    print "migration job are already already running";
		    return 1;
		}
	    }
	}
    }
}

sub check_hagroup_antiaffinity {
    my ($node, $hagroup) = @_;

    return if !$hagroup->{antiaffinity};

    my $sc = PVE::HA::Env::PVE2::read_service_config();
    #check if other vm already exist on target node in same antiaffinity group
    foreach my $sid (keys %{$sc}) {
	my $service = $sc->{$sid};
	return 1 if $service->{node} eq $node && $service->{group} eq $hagroup->{name};
    }
}


#from PVE::API2::Nodes
sub create_migrate_worker {
    my ($nodename, $type, $vmid, $target) = @_;

    my $upid;
    if ($type eq 'lxc') {
        my $online = PVE::LXC::check_running($vmid) ? 1 : 0;
        print STDERR "Migrating CT $vmid\n";
        $upid = PVE::API2::LXC->migrate_vm({node => $nodename, vmid => $vmid, target => $target,
                                            restart => $online });
    } elsif ($type eq 'qemu') {
        my $online = PVE::QemuServer::check_running($vmid, 1) ? 1 : 0;
        print STDERR "Migrating VM $vmid\n";
        $upid = PVE::API2::Qemu->migrate_vm({node => $nodename, vmid => $vmid, target => $target,
                                             online => $online });
    } else {
        die "unknown VM type '$type'\n";
    }

    my $res = PVE::Tools::upid_decode($upid);

    return $res->{pid};
};

sub get_filtered_vmlist {
    my ($nodename, $vmfilter, $templates, $ha_managed) = @_;

    my $vmlist = PVE::Cluster::get_vmlist();
    my $vms_allowed = {};
    if (defined($vmfilter)) {
        foreach my $vmid (PVE::Tools::split_list($vmfilter)) {
            $vms_allowed->{$vmid} = 1;
        }
    }

    my $res = {};
    foreach my $vmid (keys %{$vmlist->{ids}}) {
        next if %$vms_allowed && !$vms_allowed->{$vmid};
        my $d = $vmlist->{ids}->{$vmid};
        next if $nodename && $d->{node} ne $nodename;

        eval {
            my $class;
            if ($d->{type} eq 'lxc') {
                $class = 'PVE::LXC::Config';
            } elsif ($d->{type} eq 'qemu') {
                $class = 'PVE::QemuConfig';
            } else {
                die "unknown VM type '$d->{type}'\n";
            }

            my $conf = $class->load_config($vmid, $nodename);

            return if !$templates && $class->is_template($conf);
            return if !$ha_managed && PVE::HA::Config::vm_is_ha_managed($vmid);
            $res->{$vmid}->{conf} = $conf;
            $res->{$vmid}->{type} = $d->{type};
            $res->{$vmid}->{class} = $class;
        };
        warn $@ if $@;
    }

    return $res;
};


