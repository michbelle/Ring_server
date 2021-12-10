#!/usr/bin/perl -w
#
# Metasys: maintain a group of processes
#
# The primary task of this script is to manage a list of processes:
# starting, stop and re-starting them when needed.  The console output
# (stdout and stderr) of each managed process is redirected to a
# process-specific log file.  If desired email reports will be sent at
# startup, at shutdown and when a process dies.  Additionally regular
# system reports can be sent at daily or hourly intervals.
#
# All Metasys configuration parameters including the list of processes
# to manage are specified in a simple config file.  Each process must
# be assigned a unique label which is used to create the
# process-specific log files and to identify the process in the
# metasys log and notification messages.  Processes may also be
# optionally grouped/tiered for faster startup and shutdown sequences.
#
# By default Metasys will put itself in the background (daemonize)
# during startup.  To shutdown a running Metasys either execute the
# script with the "-s" option or send the running script a TERM signal.
#
# If the Proc::ProcessTable module is available the report emails will
# include process usage (cpu, memory, etc) details when available (the
# module does not always report all details on all systems).
#
# The script will print an example configuration file if the -C option
# is specified.  The example configuration lists all recognized
# parameters and serves as documentation for each one.
#
# Author: Chad Trabant, IRIS Data Management Center

use strict;
use Getopt::Long qw(:config no_ignore_case bundling);
use Cwd qw(abs_path);
use Time::HiRes qw (sleep);
use POSIX qw(mktime setsid :sys_wait_h);
use IO::Handle;
use Net::SMTP;

my $version = "2009.148";
my $help = undef;
my $verbose = 0;
my $shutdown = undef;
my $pconfig = undef;

my $mta = "localhost";	 # Mail server for sending email messages
my $logdir = "logs";	 # Directory to write process and metasys logs

my $startdelay = 10;
my $restartdelay = 30;
my $termwait = 30;
my @email = ();
my $description = '';
my $sysreport = '';
my $sysreportint = undef;
my $sysreporttime = undef;
my $htmlreport = '';
my $htmlreportint = 60;
my $htmlreporttime = undef;

# Parse command line arguments
my $getoptsret = GetOptions ( 'help|h'       => \$help,
                              'verbose|v+'   => \$verbose,
                              'shutdown|s|k' => \$shutdown,
                              'pconfig|C'    => \$pconfig,
			    );

# Print config and exit if requested
&PrintConfig if ( defined $pconfig );

# Print simple help message
if ( $#ARGV < 0 ) {
  print "Metasys ($version): maintain a list of processes\n\n";
  print "Usage: metasys [-hvskC] <config.msys>\n\n";
  print " -h       Print this help message\n";
  print " -v       Be more verbose\n";
  print " -s,-k    Shutdown running Metasys\n";
  print " -C       Print an example config file\n";
  print "\n";
  exit (1);
}

# Check for configuration file
die "Cannot find config file $ARGV[0]\n" if ( ! -f "$ARGV[0]" );

# Determine full path of configuration, hostname and username
my $config = abs_path ($ARGV[0]);
my $hostname = `uname -n`; chomp ($hostname);
my $username = (getpwuid($<))[0] || "UNKNOWN"; chomp ($username);

# Global hashes for process tracking
my %pid = ();		   # Process ID by label ($pid{label}=ID)
my %pcmd = ();		   # Process command by label ($pcmd{label}=CMD)
my %pstart = ();           # Process start time by label ($pstart{label}=time), 0 if running, -1 to terminate
my %pstarted = ();         # Process start time tracking by label ($pstarted{label}=time)
my %prestarted = ();	   # Process restart count

my @proclist = ();	   # List of all process labels in execution order
my @procnogroup = ();	   # Non-grouped process labels in config file order
my %procgroup = ();	   # Process groups with lists of labels in config file order

my $started = undef;	   # Track Metasys start time
my $cftime = undef;	   # Time stamp of config file

# Make sure the current and local bin directories are in the path
$ENV{PATH} .= ':bin:.';

print STDERR "Metasys version $version\n\n";

# Read config file
my $cferrors = &ProcessConfig;

# Exit if there were errors in the config file
if ( defined $cferrors ) {
  print STDERR "Errors in config file:\n";
  print STDERR $cferrors;
  exit (1);
}

my $logfile = "$logdir/metasys.log";
my $pidfile = "$logdir/metasys.pid";
my $termfile = "$logdir/metasys.term";

# Check for log directory and try to create if needed
if ( ! -d "$logdir" ) {
  mkdir ("$logdir", 0777) || die "Cannot create log directory: $logdir\n";
}

# Check for currently running metasys
if ( -f "$pidfile" ) {
  # Get running PID from file
  open (PID, "<$pidfile") || die "Cannot open PID file '$pidfile': $!\n";
  my $rpid = do { local $/, <PID> }; chomp ($rpid);
  close PID;
    
  # Check if PID is currently running
  if ( kill (0, $rpid) ) {
    # Set shutdown signal if requested
    if ( defined $shutdown ) {
      print STDERR "Shutting down running metasys (pid: $rpid)\n";
      &TermHandler;
      exit (0);
    } else {
      print STDERR "Metasys is already running as pid $rpid\n";
      exit (0);
    }
  } elsif ( defined $shutdown ) {
    print STDERR "Metasys instance is not currently running\n";
    print STDERR "No pid $rpid could be found, clearing pid file\n";
    if ( ! unlink ($pidfile) ) {
      print STDERR "Cannot unlink $pidfile: $!\n";
    }
    exit (0);
  }
} elsif ( defined $shutdown ) {
  print STDERR "Metasys instance is not currently running\n";
  exit (0);
}

# Clear termination signal file if present
if ( -f "$termfile" ) {
  unlink ($termfile) || die "Cannot remove termination signal file: $!\n";
}

# Set signal handers for SIGINT and SIGTERM
$SIG{'INT'} = 'TermHandler';
$SIG{'TERM'} = 'TermHandler';

# Daemonize this script
print STDERR "Moving metasys to background\n";
&Daemonize;

# Open Metasys log file and re-direct STDERR there
print STDERR "Opening log file: $logfile\n" if ( $verbose >= 1 );
open (MLOG, ">>$logfile") || die "Cannot open $logfile: $!\n";
MLOG->autoflush(1);

# Save PID
my $mpid = $$;
print STDERR "Saving PID $mpid to $pidfile\n" if ( $verbose >= 1 );
open (PID, ">$pidfile") || die "Cannot open PID file '$pidfile': $!\n";
print PID "$mpid\n";
close PID;

# Re-direct STDERR to log file
open (STDERR, '>&MLOG') || die "Cannot re-direct stderr: $!\n";

&tlog (qq{Metasys starting ($version)});

# Loop until a termination file is present
while ( ! -f "$termfile" ) {
  
  # Process config file if modification time has changed
  if ( (-M "$config") != $cftime ) {
    my $cferrors = &ProcessConfig;
    
    # Log and e-mail any config file errors
    if ( $cferrors ) {
      &tlog ("Errors in config file:\n" . $cferrors);
      &SendError ("Errors in config file", $cferrors);
    }
  }
  
  # Check for processes that have returned
  foreach my $proc ( keys %pid ) {
    if ( $pid{$proc} != -1 && waitpid ($pid{$proc}, WNOHANG) == $pid{$proc} ) {
      my $exit_status = $? >> 8;
      my $dumped_core = $? & 128;
      
      # If the process died within $restartdelay seconds use an increased delay
      if ( (time - $pstarted{$proc}) <= $restartdelay ) {
	my $moredelay =  $restartdelay * 100;
	&tlog ("$proc (pid $pid{$proc}) died too quickly (exit value $exit_status), waiting $moredelay seconds to restart");
	my $message = "Metasys - $description\n\n";
	$message .= "$proc (pid $pid{$proc}) died too quickly (exit value $exit_status)\n";
	$message .= "CORE was dumped\n" if ( $dumped_core );
	$message .= "Scheduling restart in $moredelay seconds\n";
	&SendError ("Metasys: $proc (pid $pid{$proc}) died too quickly (exit value $exit_status)", $message);
	$pstart{$proc} = time + $moredelay;
	$prestarted{$proc}++;
      }
      # Otherwise schedule the process to restart after $restartdelay seconds
      else {
	&tlog ("$proc (pid $pid{$proc}) died with exit value $exit_status, waiting $restartdelay seconds to restart");
	my $message = "Metasys - $description\n\n";
	$message .= "$proc (pid $pid{$proc}) died with exit value $exit_status\n";
	$message .= "CORE was dumped\n" if ( $dumped_core );
	$message .= "Scheduling restart in $restartdelay seconds\n";
	&SendError ("Metasys: $proc (pid $pid{$proc}) died with exit value $exit_status", $message);
	$pstart{$proc} = time + $restartdelay;
	$prestarted{$proc}++;
      }
    }
  }
  
  # Check for processes that need to be terminated
  foreach my $proc ( keys %pcmd ) {
    if ( $pstart{$proc} < 0 ) {
      &TermProcess ($proc);
      delete $pid{$proc};
      delete $pcmd{$proc};
      delete $pstart{$proc};
    }
  }
  
  # Check for processes that need to be executed
  # Create list (startlist) of non-grouped processes with pstart <= current time
  my $ctime = time;
  my @startlist = ();
  foreach my $proc ( @procnogroup ) {
    push (@startlist, $proc) if ( $pstart{$proc} > 0 && $pstart{$proc} <= $ctime );
  }
  # Execute identified processes delaying $startdelay seconds between
  foreach my $idx ( 0..$#startlist ) {
    # Terminate the process if it is already running
    if ( exists $pid{$startlist[$idx]} && $pid{$startlist[$idx]} > 0 ) {
      &TermProcess ($startlist[$idx]);
      sleep ($startdelay);
    }
    
    $pid{$startlist[$idx]} = &ExecProcess ($startlist[$idx], $pcmd{$startlist[$idx]});
    $pstart{$startlist[$idx]} = 0;
    
    # Trap door if the system has been terminated
    last if ( -f "$termfile" );
    
    sleep ($startdelay) if ( $idx != $#startlist );
  }
  
  # Check for processes in the process groups that need to be started
  my @groups = sort keys %procgroup;
  
  # Sleep if non-grouped processes were started and about to start grouped processes
  sleep ($startdelay) if ( $#groups >= 0 && $#startlist >= 0 );
  
  foreach my $gidx ( 0..$#groups ) {
    # Trap door if the system has been terminated
    last if ( -f "$termfile" );
    
    my @startlist = ();
    foreach my $proc ( @{$procgroup{$groups[$gidx]}} ) {
      push (@startlist, $proc) if ( $pstart{$proc} > 0 && $pstart{$proc} <= $ctime );
    }
    # Execute group identified processes
    foreach my $idx ( 0..$#startlist ) {
      # Terminate the process if it is already running
      if ( exists $pid{$startlist[$idx]} && $pid{$startlist[$idx]} > 0 ) {
	&TermProcess ($startlist[$idx]);
	sleep ($startdelay);
      }
      
      # Trap door if the system has been terminated
      last if ( -f "$termfile" );
      
      $pid{$startlist[$idx]} = &ExecProcess ($startlist[$idx], $pcmd{$startlist[$idx]});
      $pstart{$startlist[$idx]} = 0;
    }
    
    # Trap door if the system has been terminated
    last if ( -f "$termfile" );
    
    # Delay $startdelay seconds between groups
    sleep ($startdelay) if ( $gidx != $#groups );
  }
  
  # Send startup report
  if ( ! defined $started ) {
    $started = time;
    &SendReport ("Metasys started: $description");
  }

  # Send system report
  if ( defined $sysreporttime && $sysreporttime <= time ) {
    $sysreporttime = (&CalcIntWin (time, $sysreportint))[1];
    &SendReport ("Metasys report: $description");
  }

  # Write HTML report
  if ( defined $htmlreporttime && $htmlreporttime <= time ) {
    while ( $htmlreporttime <= time ) {
      $htmlreporttime += $htmlreportint;
    }
    &WriteHTMLReport ();
  }

  # Sleep for 1 second
  sleep 1;
}

&tlog ("Terminating all processes");

# Terminate all processes in reverse order of execution
foreach my $proc ( reverse @proclist ) {
  &TermProcess ($proc);
}

# Remove metasys pid and term file
&tlog ("Removing PID file") if ( $verbose >= 1 );
if ( ! unlink ($pidfile) ) {
  print MLOG "Cannot unlink $pidfile: $!\n";
}
&tlog ("Removing termination signal file") if ( $verbose >= 1 );
if ( ! unlink ($termfile) ) {
  print MLOG "Cannot unlink $termfile: $!\n";
}

# Send shutdown report
&SendReport ("Metasys shutdown: $description");

&tlog ("Metasys terminated.");

# Close metasys log file
close MLOG;

## End of main


######################################################################
# Process the config file
#
# Return error description string or undef on success
######################################################################
sub ProcessConfig {
  my $errors = undef;
  
  &tlog ("Processing config file") if ( defined $cftime );
  
  if ( ! open (CF, "<$config") ) {
    return "Cannot open config file $config: $!\n";
  }
  
  # Set default description
  $description = "$hostname:$config";
  
  my $ctime = time;     # Current time
  @proclist = ();	# Reset list of processes
  @procnogroup = ();    # Reset non-grouped list of processes
  %procgroup = ();	# Reset grouped lists of processes
  
  # Process config file line-by-line
  foreach my $line (<CF>) {
    # Skip comment lines beginning with #
    next if ( $line =~ /^#/ );
    
    chomp ($line);
    
    if ( $line =~ /^Process\s/i ) {
      my ($proc, $cmd) = $line =~ /^Process\s+([-\w]+)\s+(.*)$/i;
      
      if ( ! defined $proc || ! defined $cmd ) {
	$errors .= "Cannot parse Process line: '$line'\n";
      } else {
	$cmd =~ s/\s+$//;	# Trim trailing spaces
	
	if ( grep (/$proc/, @proclist) ) {
	  $errors .= "Duplicate process: '$proc'\n";
	}
	else {
  	  &tlog ("Adding $proc to process list") if ( $verbose && defined $cftime );
	  push (@procnogroup, $proc);
	}
	
	# If the process exists check if the command has changed
	if ( exists $pcmd{$proc} && $pcmd{$proc} ne $cmd ) {
	  &tlog ("$proc: command line changed") if ( defined $cftime );
	  
	  # Update command
	  $pcmd{$proc} = $cmd;
	  
	  # Trigger restart by setting start time
	  $pstart{$proc} = $ctime;
	}
	
	# Otherwise add the command to the process list
	if ( ! exists $pcmd{$proc} ) {
	  $pcmd{$proc} = $cmd;
	  $pid{$proc} = -1;
	  $pstart{$proc} = $ctime;
	  $prestarted{$proc} = 0;
	  push (@proclist, $proc);
	}
      }
    } # End of Process
    if ( $line =~ /^Process\w+\s/i ) {
      my ($group, $proc, $cmd) = $line =~ /^Process(\w+)\s+([-\w]+)\s+(.*)$/i;
      
      if ( ! defined $group || ! defined $proc || ! defined $cmd ) {
	$errors .= "Cannot parse Process[group] line: '$line'\n";
      } else {
	$cmd =~ s/\s+$//;	# Trim trailing spaces
	
	if ( grep (/$proc/, @proclist) ) {
	  $errors .= "Duplicate process: '$proc'\n";
	}
	else {
  	  &tlog ("Adding $proc to group ($group) process list") if ( $verbose && defined $cftime );
	  push (@{$procgroup{$group}}, $proc);
	}
	
	# If the process exists check if the command has changed
	if ( exists $pcmd{$proc} && $pcmd{$proc} ne $cmd ) {
	  &tlog ("$proc: command line changed") if ( defined $cftime );
	  
	  # Update command
	  $pcmd{$proc} = $cmd;
	  
	  # Trigger restart by setting start time
	  $pstart{$proc} = $ctime;
	}
	
	# Otherwise add the command to the process list
	if ( ! exists $pcmd{$proc} ) {
	  $pcmd{$proc} = $cmd;
	  $pid{$proc} = -1;
	  $pstart{$proc} = $ctime;
	  $prestarted{$proc} = 0;
	  push (@proclist, $proc);
	}
      }
    } # End of Process[group]
    elsif ( $line =~ /^Email\s/i ) {
      # Regex to test for valid email address
      my $validemailre = q{^([0-9a-zA-Z]([-.\w]*[0-9a-zA-Z])*@(([0-9a-zA-Z])+([-\w]*[0-9a-zA-Z])*\.)+[a-zA-Z]{2,9})$};
      
      my ($caddr) = $line =~ /^Email\s+(.*)/i;
      $caddr =~ s/\s+$// if ( defined $caddr ); # Trim trailing spaces

      if ( defined $caddr ) {
	my @newemail = ();

	# Loop over specified addresses and validate them
	foreach my $addr ( split (/[\s,]+/, $caddr) ) {
	  if ( $addr =~ /@/ && $addr !~ /${validemailre}/) {
	    $errors .= "Email address '$addr' is invalid\n";
	  } else {
	    # Add email address to list if not already included
	    push (@newemail, $addr) if ( ! grep (/$addr/, @newemail) );
	  }
	}

	# Reset email address list only if valid addresses were found
	@email = @newemail if ( scalar @newemail );
      } else {
	@email = ();
      }
    } # End of Email
    elsif ( $line =~ /^MTA\s/i ) {
      my ($cmta) = $line =~ /^MTA\s+(.*)$/;
      $cmta =~ s/\s+$// if ( defined $cmta ); # Trim trailing spaces
      
      # Sanity check MTA value
      if ( defined $cmta && $cmta =~ /[-\.\w]+/ ) {
	$mta = $cmta;
      } else {
	$errors .= "Error with MTA setting: '$cmta'\n";
      }
    } # End of MTA
    elsif ( $line =~ /^StartDelay\s/i ) {
      my ($cstartdelay) = $line =~ /^StartDelay\s+(.*)$/;
      
      $cstartdelay =~ s/\s+$// if ( defined $cstartdelay ); # Trim trailing spaces
      
      # Sanity check StartDelay value
      if ( defined $cstartdelay && $cstartdelay =~ /\d+/ ) {
	$startdelay = $cstartdelay;
      } else {
	$errors .= "Error with StartDelay setting: '$cstartdelay'\n";
      }
    } # End of StartDelay
    elsif ( $line =~ /^RestartDelay\s/i ) {
      my ($crestartdelay) = $line =~ /^RestartDelay\s+(.*)$/;
      
      $crestartdelay =~ s/\s+$// if ( defined $crestartdelay ); # Trim trailing spaces
      
      # Sanity check RestartDelay value
      if ( defined $crestartdelay && $crestartdelay =~ /\d+/ ) {
	$restartdelay = $crestartdelay;
      } else {
	$errors .= "Error with RestartDelay setting: '$crestartdelay'\n";
      }
    } # End of RestartDelay
    elsif ( $line =~ /^TermWait\s/i ) {
      my ($ctermwait) = $line =~ /^TermWait\s+(.*)$/;
      
      $ctermwait =~ s/\s+$// if ( defined $ctermwait ); # Trim trailing spaces
      
      # Sanity check TermWait value
      if ( defined $ctermwait && $ctermwait =~ /\d+/ ) {
	$termwait = $ctermwait;
      } else {
	$errors .= "Error with TermWait setting: '$ctermwait'\n";
      }
    } # End of TermWait
    elsif ( $line =~ /^Description\s/i ) {
      my ($cdescription) = $line =~ /^Description\s+(.*)$/;
      
      $cdescription =~ s/\s+$// if ( defined $cdescription ); # Trim trailing spaces
      
      # Set description
      if ( defined $cdescription ) {
	$description = $cdescription;
      } else {
	$errors .= "Error with Description setting: '$cdescription'\n";
      }
    } # End of Description
    elsif ( $line =~ /^SysReport\s/i ) {
      my ($csysreport) = $line =~ /^SysReport\s+(.*)$/;
      
      $csysreport =~ s/\s+$// if ( defined $csysreport ); # Trim trailing spaces
      
      # Sanity check SysReport value
      if ( defined $csysreport && $csysreport =~ /^Daily$/i ) {
	$sysreport = $csysreport;
	$sysreportint = 86400;
	$sysreporttime = (&CalcIntWin (time, $sysreportint))[1];
      } elsif ( defined $csysreport && $csysreport =~ /^Hourly$/i ) {
	$sysreport = $csysreport;
	$sysreportint = 3600;
	$sysreporttime = (&CalcIntWin (time, $sysreportint))[1];
      } else {
	$errors .= "Error with SysReport setting: '$csysreport'\n";
      }
    } # End of SysReport
    elsif ( $line =~ /^HTMLReport\s/i ) {
      my ($chtmlreport) = $line =~ /^HTMLReport\s+(.*)$/;
      
      $chtmlreport =~ s/\s+$// if ( defined $chtmlreport ); # Trim trailing spaces
      
      # Sanity check SysReport value
      if ( defined $chtmlreport ) {
	# If HTML report file name is followed by ":###" a interval has been specified
	if ( $chtmlreport =~ /\:\d+$/ ) {
	  ($htmlreport, $htmlreportint) = $chtmlreport =~ /^(.*)\:(\d+)$/;
	} else {
	  $htmlreport = $chtmlreport;
	}
	
	$htmlreporttime = (&CalcIntWin (time, $htmlreportint))[0];
      } else {
	$errors .= "Error with HTMLReport setting: '$chtmlreport'\n";
      }
    } # End of HTMLReport
    # Only process LogDir setting during startup
    elsif ( $line =~ /^LogDir\s/i && ! defined $cftime ) {
      my ($clogdir) = $line =~ /^LogDir\s+(.*)$/;
      
      $clogdir =~ s/\s+$// if ( defined $clogdir ); # Trim trailing spaces
      
      # Sanity check LogDir value
      if ( defined $clogdir && $clogdir =~ /[-\w\/\. ]+/ ) {
	$logdir = $clogdir;
      } else {
	$errors .= "Error with LogDir setting: '$clogdir'\n";
      }
    } # End of LogDir
  } # End of parsing config file
  
  close (CF);
  
  # Rebuild @proclist to be in execution order
  @proclist = ();
  push (@proclist, @procnogroup);
  foreach my $group ( sort keys %procgroup ) {
    push (@proclist, @{$procgroup{$group}});
  }
  
  # Check current process list against those in the config file and
  # mark those not found for termination.
  foreach my $rproc ( keys %pcmd ) {
    $pstart{$rproc} = -1 if ( ! grep (/$rproc/, @proclist) );
  }

  # Update config file time stamp
  $cftime = (-M "$config");
  
  return $errors;
} # End of ProcessConfig()


######################################################################
# Execute a process and return the process ID
######################################################################
sub ExecProcess {		# ExecProcess (proc, command)
  my $proc = shift;
  my $cmdstr = shift;
  
  # Split command into separate parts to avoid exec() invocation of /bin/sh
  # and remove any single or double quotes.
  my @cmd = ();
  foreach my $c ( split (/\s+/, $cmdstr) ) {
    $c =~ s/("|")//g;
    $c =~ s/('|')//g;
    push (@cmd, $c);
  }
  
  &tlog ("Executing $proc: '@cmd'");
  
  # Fork process
  my $spid = fork;
  
  if ( ! defined $spid ) {
    &tlog ("Fork failed.");
    return $spid;
  }
  
  # For the new child process
  if ( ! $spid ) {
    # Open processes log file, redirect stderr to same
    open (STDOUT, ">>$logdir/$proc") || die "Cannot re-open stdout => $logdir/$proc: $!\n";
    open (STDERR, ">&STDOUT") || die "Cannot re-direct stderr: $!\n";
    STDOUT->autoflush(1);
    
    # Exec the system command (replacing this child process)
    exec (@cmd);
    die "Exec of sub-process failed";
  }
  
  $pstarted{$proc} = time;
  &tlog ("Executed PID: $spid") if ( $verbose >= 1 );
  
  return $spid;
} # End of ExecProcess


######################################################################
# Terminate a process and return the process ID
######################################################################
sub TermProcess {		# TermProcess (proc)
  my $proc = shift;
  my $pid = $pid{$proc};

  my $checkinterval = 0.1;
  
  # If process has never run or been shutdown we're done
  return if ( ! defined $pid || $pid == -1 );
  
  # If process does not exist we're done
  if ( ! kill (0, $pid) ) {
    $pid{$proc} = -1;
    return;
  }
  
  &tlog ("Terminating $proc (pid $pid)") if ( $verbose > 0 );
  
  # Send process the TERM signal
  kill ('TERM', $pid);
  
  # Wait up to $termwait seconds for process to terminate
  my $count = 0;
  my $wpid;
  while ( ($wpid = waitpid ($pid, WNOHANG)) != $pid ) {
    last if ( ($count * $checkinterval) >= $termwait );
    $count++;
    sleep ($checkinterval);
  }

  # If the process terminated check the status
  if ( $wpid == $pid ) {
    my $exit_status = $? >> 8;
    my $dumped_core = $? & 128;
    
    &tlog ("$proc terminated with exit status: $exit_status");
    &tlog ("$proc dumped core!") if ( $dumped_core );
    
    $pid{$proc} = -1;
    return;
  }
  # Otherwise send the KILL signal
  else {
    &tlog ("Waited $termwait seconds, sending KILL to $proc (pid $pid)");
    kill ('KILL', $pid);
  }
  
  # Wait up to $termwait seconds for process to terminate
  $count = 0;
  while ( ($wpid = waitpid ($pid, WNOHANG)) != $pid ) {
    last if ( ($count * $checkinterval) >= $termwait );
    $count++;
    sleep ($checkinterval);
  }
  
  # If the process terminated check the status
  if ( $wpid == $pid ) {
    my $exit_status = $? >> 8;
    my $dumped_core = $? & 128;
    
    &tlog ("$proc terminated with exit status: $exit_status");
    &tlog ("$proc dumped core!") if ( $dumped_core );
    
    $pid{$proc} = -1;
    return;
  }
  # Otherwise log a warning
  else {
    &tlog ("$proc (pid $pid) did not terminate, leaving (potential) zombie");
  }
} # End of TermProcess


######################################################################
# Send an email message
######################################################################
sub SendMsg {			# sendmsg (subject, message, htmlflag)
  my $subject = shift;
  my $message = shift;
  my $htmlflag = shift;

  # Check that email addresses and subject are defined
  return if ( $#email < 0 || ! defined $subject );
  
  my $smtp = Net::SMTP->new($mta, Timeout => 60);
  
  if ( ! defined $smtp ) {
    &tlog ("Error connecting to MTA '$mta'");
  } else {
    my $addr = join (',', @email);

    $smtp->mail("${username}");
    $smtp->to(@email);
    $smtp->data();
    $smtp->datasend("From: Metasys running as ${username}\@${hostname} <${username}\@${hostname}>\n");
    $smtp->datasend("To: $addr\n");
    $smtp->datasend("Mime-Version: 1.0\n") if ( $htmlflag );
    $smtp->datasend("Content-type: text/html; charset=\"iso-8859-1\"\n") if ( $htmlflag );
    $smtp->datasend("Subject: $subject\n\n");
    $smtp->datasend("$message");
    $smtp->dataend();
    
    $smtp->quit;
    
    &tlog ("Sent email: '$subject'");
  }
} # End of SendMsg()


######################################################################
# Send an error message
######################################################################
sub SendError {		# SendErrorReport (subject)
  my $subject = shift;
  my $message = shift;
  
  $subject = "Metasys report" if ( ! defined $subject );
  
  # Prefix location of the configuration
  $message = "${hostname}:${config}\n\n" . $message;
  
  # Send report
  &SendMsg ($subject, $message);
} # End of SendError()


######################################################################
# Send a report for the running instance of Metasys
######################################################################
sub SendReport {		# SendReport (subject)
  my $subject = shift;
  
  $subject = "Metasys report" if ( ! defined $subject );
  
  my $report = &CreateHTMLReport();
  
  # Send report
  &SendMsg ($subject, $report, 1);
} # End of SendReport()


######################################################################
# Write an HTML report for the running instance of Metasys
######################################################################
sub WriteHTMLReport {		# WriteHTMLReport
  my $ptable = undef;
  
  my $html = &CreateHTMLReport();
  
  # Write HTML report
  if ( ! open (HR, ">$htmlreport") ) {
    &tlog ("Error opening HTML report file '$htmlreport': $!");
  } else {
    print HR $html;
    close (HR);
  }
} # End of WriteHTMLReport()


######################################################################
# Create an HTML report for the running instance of Metasys
######################################################################
sub CreateHTMLReport {		# CreateHTMLReport
  my $ptable = undef;
  
  # If Proc::ProcessTable is available get the current process table
  if ( eval { require Proc::ProcessTable; 1; } ) {
    $ptable = new Proc::ProcessTable;
  }
  
  # Start HTML
  my $html = qq(<!DOCTYPE html\nPUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN"\n);
  $html .= qq("http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">\n);
  $html .= qq(<HTMl xmlns="http://www.w3.org/1999/xhtml" lang="en-US" xml:lang="en-US">\n);
  $html .= qq(<HEAD>\n);
  $html .= qq(<TITLE>Metasys: $description</TITLE>\n);
  $html .= qq(<META http-equiv="Content-Type" content="text/html; charset=iso-8859-1" />\n);
  $html .= qq(</HEAD>\n);
  
  $html .= qq(<BODY>\n);
  $html .= qq(<STYLE type="text/css">\n);
  $html .= qq(body {margin: 0; padding: 0; overflow: auto;} div {margin: 0; padding: 0;} .boldtext {font-size: x-large; font-weight: bold;}\n);
  $html .= qq(#header {position:absolute; top: 5px; left: 5px; right: 5px; height: 80px; background-color: #6699FF; text-align: center; border:1px solid #aaaaaa; border-bottom:2px solid #000000;} \n);
  $html .= qq(#body {position:absolute; top: 90px; left: 5px; right: 5px;} \n);
  $html .= qq(<!--[if IE]><style type="text/css" media="screen">#header {width: expression(document.body.clientWidth - ((2 * 5)) + "px");}#body {width: expression(document.body.clientWidth - (2 * 5) + "px");height: expression(document.body.clientHeight - (90 + (2 * 5)) + "px");}<![endif]-->\n);
  $html .= qq(</STYLE>\n);
  
  # Body header
  $html .= qq(<DIV id="header"><B><DIV style="font-size: 26px;line-height: 30px;">Metasys</DIV><BR><DIVstyle="font-size: 18px;line-height: 15px;">$description</B></DIV><DIV>\n);
  
  $html .= qq(<DIV id="body">\n);
  $html .= qq(${hostname}:${config}<BR>);
  $html .= sprintf ("Report time %s<BR>\n", &localtimestr (time));
  $html .= sprintf ("System started %s (%s ago)<BR>\n", &localtimestr ($started), &ago(time-$started));
  
  $html .= qq(<BR><BR>\n);
  
  my $pcount =  $#proclist + 1;
  $html .= qq(<SPAN class="boldtext" id="processlist">Processes ($pcount):</SPAN>\n);
  $html .= qq(<BLOCKQUOTE>\n);
  
  # List processes
  foreach my $proc ( @proclist ) {
    my $groupid = "";
    foreach my $group ( sort keys %procgroup ) {
      if ( grep (/$proc/, @{$procgroup{$group}}) ) {
	$groupid = " [$group]";
	last;
      }
    }
    
    # Print process label, ID, start time and duration
    $html .= sprintf ("<B>${proc}${groupid}</B> (pid $pid{$proc}), started %s (%s ago), restarts: %d<BR>\n",
		      (exists $pstarted{$proc}) ? &localtimestr($pstarted{$proc}) : "Never",
		      (exists $pstarted{$proc}) ? &ago(time-$pstarted{$proc}) : "0",
		      (exists $prestarted{$proc}) ? $prestarted{$proc} : 0);
    
    # If the process table is available add process details
    if ( defined $ptable && $pid{$proc} > 0 ) {
      # Find the PID in the process table
      my $p = undef;
      foreach my $o ( @{$ptable->table} ) {
	if ( $o->pid == $pid{$proc} ) {
	  $p = $o;
	  last;
	}
      }
      
      # Add process details to report
      if ( defined $p ) {
	$html .= sprintf ("&nbsp;&nbsp;%%CPU: %s, %%mem: %s, size: %s, RSS: %s, state: %s<BR>\n",
			  $p->pctcpu,$p->pctmem,$p->size,$p->rss,$p->state);
      } else {
	$html .= qq(&nbsp;&nbsp;Process not currently running<BR>\n);
      }
    }
    
    # Include command line
    $html .= "&nbsp;&nbsp;CMD: <I>$pcmd{$proc}</I><BR><BR>\n";
  }
  $html .= qq(</BLOCKQUOTE>\n);
  
  # Include critical Metasys parameters
  $html .= qq(<SPAN class="boldtext" id="parameters">System parameters:</SPAN>\n);
  $html .= qq(<BLOCKQUOTE>\n);
  $html .= sprintf "%s: <I>%s</I><BR>\n", "Email", join (', ', @email);
  $html .= sprintf "%s: <I>%s</I><BR>\n", "MTA", $mta;
  $html .= sprintf "%s: <I>%s</I><BR>\n", "StartDelay", $startdelay;
  $html .= sprintf "%s: <I>%s</I><BR>\n", "RestartDelay", $restartdelay;
  $html .= sprintf "%s: <I>%s</I><BR>\n", "TermWait", $termwait;
  $html .= sprintf "%s: <I>%s</I><BR>\n", "SysReport", $sysreport;
  $html .= sprintf "%s: <I>%s:%d</I><BR>\n", "HTMLReport", $htmlreport, $htmlreportint;
  $html .= sprintf "%s: <I>%s</I><BR>\n", "LogDir", $logdir;
  $html .= qq(</BLOCKQUOTE>\n);
  
  # Finish off HTML
  $html .= qq(</DIV>\n);
  $html .= qq(</BODY>\n);
  $html .= qq(</HTML>\n);
  
  return $html;
} # End of CreateHTMLReport()


######################################################################
# Create local time stamp from given epoch time value
######################################################################
sub localtimestr {
  my $etime = shift;
  
  return if ( ! defined $etime );
  
  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($etime);
  $year += 1900;
  $mon += 1;
  
  return sprintf ("%04d-%02d-%02d %02d:%02d:%02d",
		  $year, $mon, $mday, $hour, $min, $sec);
} # End of localtimestr()


######################################################################
# Log messages with current time stamp
######################################################################
sub tlog {			# tlog (message, options, ...)
  my $format = shift;
  my @variables = @_;
  
  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) =
    localtime(time);
  $year += 1900;
  $mon += 1;
  my $tstamp = sprintf ("%04d-%02d-%02d %02d:%02d:%02d",
			$year, $mon, $mday, $hour, $min, $sec);
  
  # Log message with time stamp
  printf MLOG "$tstamp $format\n", @variables;
} # End of tlog()


######################################################################
# Deamonize current process/script
######################################################################
sub Daemonize {
  open STDIN, '/dev/null' or die "Can't read /dev/null: $!";
  open STDOUT, '>/dev/null' or die "Can't write to /dev/null: $!";
  
  defined (my $pid = fork) or die "Can't fork: $!";
  exit if $pid;
  setsid                  or die "Can't start a new session: $!";
} # End of Daemonize()


######################################################################
# Termination signal handler
######################################################################
sub TermHandler {
  # Create termination signal file
  open (TF, ">$termfile") || die "Cannot create $termfile: $!\n";
  close (TF);
} # End of TermHandler()


######################################################################
# Calculate a normalized interval time window for a given reference
# time (usually the current time) and interval in seconds.  The
# window is always normalized relative to the current day, intervals
# which evenly divide days will work cleanly, other intervals will
# probably work but might result in unexpected window calculations.
#
# Returns the start and end times of the interval containing the
# reference time.
######################################################################
sub CalcIntWin {		# CalcIntWin (reftime, interval)
  my $reftime = shift;
  my $interval = shift;

  my ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst) = localtime($reftime);
  
  # Calculate rounded epoch time
  my $startint = POSIX::mktime (0,0,0,$mday,$mon,$year,0,0,$isdst);
  
  while ( ($startint + $interval) <= $reftime ) {
    $startint += $interval;
  }
  
  my $endint = $startint + $interval;
  
  return ($startint, $endint);
} # End of CalcIntWin


######################################################################
# Return simple time duration text based on a given number of seconds
######################################################################
sub ago {
  my $seconds = shift;

  return if ( ! defined $seconds );
  
  my $years = int ($seconds / (365 * 86400));
  my $months = int ($seconds / (30 * 86400));
  my $days = int ($seconds / 86400);
  my $hours = int ($seconds / 3600);
  my $minutes = int ($seconds / 60);
  
  if ( $years ) {
    $seconds -= $years * (365 * 86400);
    $months = int ($seconds / (30 * 86400));
    return sprintf "%d years, %d months", $years, $months;
  } elsif ( $months ) {
    $seconds -= $months * (30 * 86400);
    $days = int ($seconds / 86400);
    return sprintf "%d months, %d days", $months, $days;
  } elsif ( $days ) {
    $seconds -= $days * 86400;
    $hours = int ($seconds / 3600);
    return sprintf "%d days, %d hours", $days, $hours;
  } elsif ( $hours ) {
    $seconds -= $hours * 3600;
    $minutes = int ($seconds / 60);
    return sprintf "%d hours, %d minutes", $hours, $minutes;
  } elsif ( $minutes ) {
    $seconds -= $minutes * 60;
    return sprintf "%d minutes, %d seconds", $minutes, $seconds;
  } else {
    return sprintf "%d seconds", $seconds;
  }
} # End of ago()


######################################################################
# Print an example Metasys config file and exit
######################################################################
sub PrintConfig {
  print <<CFILE;
# Example Metasys config file

# List of processes to maintain, processes will be started in the
# order specified and shut down in the reverse order.
Process label1 process1 command line
#Process label2 process2 command line
#Process webserver httpd <httpd command line options>

# Email addresses for notification messages, space or comma separated.
# Default is no addresses (no notifications will be sent).
#Email admin\@mailhost.org, admin2\@mailhost.org

# Send messages to this MTA (mail server), required for email sending
# Default value: $mta
#MTA $mta

# Start delay in seconds, wait period between starting processes.
# Default value: $startdelay
#StartDelay $startdelay

# Restart delay in seconds, wait period to restart a process after it
# dies.  Additionally, if a process dies within the restart delay
# interval it will be scheduled for a restart in 100 times this value.
# Default value: $restartdelay
#RestartDelay $restartdelay

# Termination wait in seconds, wait period between sending TERM and KILL signals.
# Default value: $termwait
#TermWait $termwait

# Description used to identify this collection of processes.
# Default is hostname:configfile
#Description System of systems

# Send HTML formatted system reports (email) at regular intervals
# (normlized to day boundaries).  Default is no regular reports,
# possible values are 'Daily' or 'Hourly'.
#SysReport Daily

# Update an HTML formatted report file at regular intervals.  An
# optional update interval may be specified by adding ":###" to the
# end of the report file where "###" is the update interval in seconds.
# Default is no HTML reports, default interval is $htmlreportint seconds.
#HTMLReport metasys.html:60

# Log directory, directory for process logs and Metasys log and state files.
# This paramter cannot be changed after the system is started.
# Default value: $logdir
#LogDir $logdir

CFILE

  exit (0);
} # End of PrintConfig()
