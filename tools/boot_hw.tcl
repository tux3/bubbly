#!/usr/bin/env -S vivado -notrace -nolog -nojournal -mode batch -source
# Boot the FPGA. Typically used after re-flashing a cfgmem, but can reboot a running device too

open_hw_manager
connect_hw_server -allow_non_jtag
open_hw_target

boot_hw_device [get_hw_devices xc7a100t_0] -timeout 10

