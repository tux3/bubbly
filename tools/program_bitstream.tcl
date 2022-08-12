#!/usr/bin/env tclsh
# Program the FPGA with a bitstream. This is not permanent, it doesn't touch the flash.

# Need to do trickery to forward argv to vivado, can't do it with just env -S
if {[info commands "version"] == ""} {
    # Running in tclsh, which doesn't have Vivado commands.
    exec vivado -notrace -nolog -nojournal -mode batch -source $argv0 -tclargs {*}$argv >@stdout
    exit 0
}
if {$argc != 1} {
    puts "Usage: $argv0 <top.bit>"
    exit 1
}
set bitfile [lindex $argv 0]

open_hw_manager
connect_hw_server -allow_non_jtag
open_hw_target

set_property PROBES.FILE {} [get_hw_devices xc7a100t_0]
set_property FULL_PROBES.FILE {} [get_hw_devices xc7a100t_0]
set_property PROGRAM.FILE $bitfile [get_hw_devices xc7a100t_0]
program_hw_devices [get_hw_devices xc7a100t_0]

