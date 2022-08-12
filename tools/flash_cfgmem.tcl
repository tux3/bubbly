#!/usr/bin/env tclsh
# Program the FPGA flash with the MCS and PRM files passed in argument

# Need to do trickery to forward argv to vivado, can't do it with just env -S
if {[info commands "version"] == ""} {
    # Running in tclsh, which doesn't have Vivado commands.
    exec vivado -notrace -nolog -nojournal -mode batch -source $argv0 -tclargs {*}$argv >@stdout
    exit 0
}

if {$argc != 2} {
    puts "Usage: $argv0 <cfgmem.mcs> <cfgmem.prm>"
    exit 1
}
set mcs_file [lindex $argv 0]
set prm_file [lindex $argv 1]

open_hw_manager
connect_hw_server -allow_non_jtag
open_hw_target

set hwdev [lindex [get_hw_devices xc7a100t_0] 0]

current_hw_device [get_hw_devices xc7a100t_0]
refresh_hw_device -update_hw_probes false $hwdev

set cfgmem [get_hw_cfgmems -quiet]
if {$cfgmem == ""} {
    set cfgmem [create_hw_cfgmem -hw_device $hwdev [lindex [get_cfgmem_parts {s25fl128sxxxxxx0-spi-x1_x2_x4}] 0]]
}

set_property PROGRAM.ADDRESS_RANGE  {use_file} $cfgmem
set_property PROGRAM.FILES [list $mcs_file ] $cfgmem
set_property PROGRAM.PRM_FILE $prm_file $cfgmem
set_property PROGRAM.UNUSED_PIN_TERMINATION {pull-none} $cfgmem
set_property PROGRAM.BLANK_CHECK  0 $cfgmem
set_property PROGRAM.ERASE  1 $cfgmem
set_property PROGRAM.CFG_PROGRAM  1 $cfgmem
set_property PROGRAM.VERIFY  1 $cfgmem
set_property PROGRAM.CHECKSUM  0 $cfgmem

startgroup
create_hw_bitstream -hw_device $hwdev [get_property PROGRAM.HW_CFGMEM_BITFILE $hwdev]
program_hw_devices $hwdev
refresh_hw_device $hwdev
program_hw_cfgmem -hw_cfgmem [ get_property PROGRAM.HW_CFGMEM $hwdev]
endgroup

