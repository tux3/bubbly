MEMORY
{
  RAM : ORIGIN =   0x8000000000, LENGTH = 32K
}

ENTRY(start);

SECTIONS
{
  .start ORIGIN(RAM) :
  {
    KEEP(*(.start));
  } > RAM

  .trap_handler : ALIGN(4)
  {
    *(.trap_handler .trap_handler.*);
  } > RAM

  .text :
  {
    *(.text .text.*);
  } > RAM
}
