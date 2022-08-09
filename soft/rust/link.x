MEMORY
{
  FLASH : ORIGIN = 0x00000000000, LENGTH = 16M
  RAM : ORIGIN =   0x18000000000, LENGTH = 4K
}

ENTRY(start);

SECTIONS
{
  .start ORIGIN(FLASH) :
  {
    KEEP(*(.start));
  } > FLASH

  .text :
  {
    *(.text .text.*);
  } > FLASH
}
