MEMORY
{
  RAM : ORIGIN =   0x000000000000, LENGTH = 16M
}

ENTRY(start);

SECTIONS
{
  .start ORIGIN(RAM) :
  {
    KEEP(*(.start));
  } > RAM

  .text :
  {
    *(.text .text.*);
  } > RAM

  .trap_handler : ALIGN(4)
  {
    *(.trap_handler .trap_handler.*);
  } > RAM

  .data :
  {
    *(.data .data.*);
  } > RAM

  .rodata :
  {
    *(.rodata .rodata.*);
  } > RAM
}
