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
if {$status == "Queued..." || [string match "Running*" $status]} {
    puts "Run $run seems to already be running (status \"$status\")"
} else {
    launch_runs $run -to_step write_bitstream -jobs 8
}

wait_on_runs $run

