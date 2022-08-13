foreach mod_inst [get_cells -hier -filter {(ORIG_REF_NAME == axi4lite_platform || REF_NAME == axi4lite_platform)}] {
    set src_clk [get_clocks -of_objects [get_pins $mod_inst/mtime_tick_sync_reg[0]/D]]
    set_false_path -from $src_clk -to [get_cells -quiet "$mod_inst/mtime_tick_sync_reg[0]"]
    
    set mtime_tick_ffs [get_cells -quiet -hier -regexp ".*/mtime_tick_sync_reg\\\[\[0-9\]+\\\]" -filter "PARENT == $mod_inst"]
    if {[llength $mtime_tick_ffs]} {
        set_property ASYNC_REG TRUE $mtime_tick_ffs
    }
}