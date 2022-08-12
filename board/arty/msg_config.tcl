# NOTE: Be careful with messages set to INFO, if they reach the default limit (100), this will suppress ALL further messages!
#       If we only do -new_severity INFO instead of suppressing, and we don't increase the limit, this could hide real warnings

## Global allow
# Cannot add Board Part, board_part file not available
set_msg_config -id {[Board 49-26]} -suppress
# Design top has port driven by constant 0
set_msg_config -id {[Synth 8-3917]} -suppress
# Parallel synthesis criteria not met
set_msg_config -id {[Synth 8-7080]} -new_severity INFO
# Auto Incremental Compile:: No reference checkpoint was found
set_msg_config -id {[Vivado 12-7122]} -new_severity INFO

# No cells matched regex in tcl file
set_msg_config -id {[Vivado 12-180]} -new_severity INFO
# -delay time will be rounded to ensure it is an integer multiple of 1 picosecond
set_msg_config -id {[Vivado 12-2489]} -new_severity INFO
# Use of 'set_input_delay' with '-reference_pin' is not supported by synthesis. The constraint will not be passed to synthesis.
set_msg_config -id {[Designutils 20-1567]} -new_severity INFO
# Found switching activity that implies high-fanout reset nets being asserted for excessive periods of time which may result in inaccurate power analysis.
set_msg_config -id {[Power 33-332]} -new_severity INFO
# There are set_bus_skew constraint(s) in this design. Please run report_bus_skew to ensure that bus skew requirements are met.
set_msg_config -id {[Timing 38-436]} -new_severity INFO

## Increased warnings
# Port is either unconnected or has no load
set_msg_config -id {[Synth 8-7129]} -new_severity {CRITICAL WARNING}

## Specific allowed warnings
# Sequential element is unused and will be removed from module
set_msg_config -id {[Synth 8-3332]} -string {"from module fixp_mult."} -suppress

## Warnings in third party code
# set_false_path : Empty to list for constraint
set_msg_config -id {[Synth 8-3321]} -string {"axis_async_fifo.tcl"} -new_severity INFO
# Unused sequential element was removed
set_msg_config -id {[Synth 8-6014]} -string {"element COUNT_PENDING"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element ptp_ts_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element m_axis_ptp_ts"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element temp_tid_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element temp_tdest_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element m_axis_tkeep_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element m_axis_tid_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element m_axis_tdest_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element temp_m_axis_t"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element wr_ptr_temp_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element send_frame_reg_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element rd_ptr_temp_reg"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element busy_reg_suppress_8_6014"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element save_axis_t"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element save_eth_payload_axis_t"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element m_eth_payload_axis"} -suppress
set_msg_config -id {[Synth 8-6014]} -string {"element temp_m_eth_payload_axis"} -suppress
# Port is either unconnected or has no load
set_msg_config -id {[Synth 8-7129]} -string {"in module eth_arb_mux "} -suppress
set_msg_config -id {[Synth 8-7129]} -string {"in module axis_async_fifo__parameterized"} -suppress
set_msg_config -id {[Synth 8-7129]} -string {"in module axis_adapter__parameterized"} -suppress
set_msg_config -id {[Synth 8-7129]} -string {"in module axis_async_fifo "} -suppress
set_msg_config -id {[Synth 8-7129]} -string {"in module axis_adapter "} -suppress
set_msg_config -id {[Synth 8-7129]} -string {"in module axis_gmii_tx "} -suppress
