# TinyFPGA BX's clock (16,000,000Hz)
create_clock  -period 62.50 -name {CLK_16MHZ} [get_ports {CLK_16MHZ}]

# Assume the SPI clock will never go above 8MHZ
create_clock  -period 125 -name {SPI_CLK} [get_ports {SPI_CLK}]
