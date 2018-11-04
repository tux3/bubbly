FPGA_FAMILY=ice40
FPGA_MODEL=lp8k
FPGA_PACKAGE=cm81

TARGET_FREQ_MHZ=32

SRCDIR=./src
BINDIR=./build
PRJ=$(notdir ${PWD})
SRCFILES=$(filter-out $(wildcard ${SRCDIR}/**_tb.v), $(wildcard ${SRCDIR}/**.v)) # Take all .v files, except testbenches

all: ${BINDIR}/${PRJ}.bin
	

clean:
	rm -f $(wildcard ${BINDIR}/${PRJ}.*)

flash: ${BINDIR}/${PRJ}.bin
	rsync -avzh "$^" "pi:/tmp/${PRJ}.bin"
	ssh pi tinyprog -p "/tmp/${PRJ}.bin"

${BINDIR}/${PRJ}.bin: ${BINDIR}/${PRJ}.asc
	icepack ${BINDIR}/${PRJ}.asc ${BINDIR}/${PRJ}.bin

${BINDIR}/${PRJ}.asc: ${BINDIR}/${PRJ}.json
	nextpnr-${FPGA_FAMILY} --${FPGA_MODEL} --package ${FPGA_PACKAGE} --json ${BINDIR}/${PRJ}.json --pcf ${SRCDIR}/constraints/pins.pcf --freq ${TARGET_FREQ_MHZ} --asc ${BINDIR}/${PRJ}.asc --seed 0

${BINDIR}/${PRJ}.json: ${SRCFILES}
	yosys -p "synth_${FPGA_FAMILY} -top top -json ${BINDIR}/${PRJ}.json -blif ${BINDIR}/${PRJ}.blif" $^

