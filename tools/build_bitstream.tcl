#!/usr/bin/env tclsh
# Run synthesis, implementation, and build a bitstream

# Need to do trickery to forward argv to vivado, can't do it with just env -S
if {[info commands "version"] == ""} {
    # Running in tclsh, which doesn't have Vivado commands.
    exec vivado -notrace -nolog -nojournal -mode batch -source $argv0 -tclargs {*}$argv >@stdout
    exit 0
}
if {$argc != 2} {
    puts "Usage: $argv0 <bubbly.xpr> impl_1"
    exit 1
}
set prj [lindex $argv 0]
set run [lindex $argv 1]

open_project $prj
update_compile_order -fileset sources_1

set status [get_property STATUS [get_runs $run]]
set parent [get_property PARENT [get_runs $run]]
set parent_status [get_property STATUS [get_runs $parent]]
set needs_refresh [get_property NEEDS_REFRESH [get_runs $run]]
set parent_needs_refresh [get_property NEEDS_REFRESH [get_runs $parent]]

if {$status == "Queued..." || [string match "Running*" $status]} {
    if {$status == "Queued..." && [string match "Running*" $parent_status]} {
        puts "Run $run seems to be queued, waiting on parent"
        wait_on_runs $parent
    } else {
        puts "Run $run seems to already be running (status \"$status\")"
    }
} elseif {$needs_refresh || $parent_needs_refresh} {
    puts "Run $run appears to be out of date, resetting it"
    reset_run $parent
    launch_runs $run -to_step write_bitstream -jobs 8
    wait_on_runs $parent
} else {
    launch_runs $run -to_step write_bitstream -jobs 8
    wait_on_runs $parent
}

wait_on_runs $run

