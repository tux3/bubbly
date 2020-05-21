FPGA_FAMILY=ice40
FPGA_MODEL=lp8k
FPGA_PACKAGE=cm81

TARGET_FREQ_MHZ=32

SRCDIR=./src
BINDIR=./build
PRJ=$(notdir ${PWD})
SRCFILES_UNORDERED=$(filter-out $(shell find ${SRCDIR}/test/ -name *.v -or -name *.sv), ${SRCDIR}/global.svh $(shell find ${SRCDIR} -name *.v -or -name *.sv))

$(info Analyzing compilation order...)
SRCFILES=$(shell sv_auto_order ${SRCFILES_UNORDERED})

all: ${BINDIR}/${PRJ}.bin
	

clean:
	rm -f $(wildcard ${BINDIR}/${PRJ}.*)

check:
	yosys -f "verilog -sv" -p "read_verilog -icells -lib +/${FPGA_FAMILY}/cells_sim.v; hierarchy; proc; check;" ${SRCFILES}

flash: ${BINDIR}/${PRJ}.bin
	rsync -avzh "$^" "pi:/tmp/${PRJ}.bin"
	ssh pi tinyprog -p "/tmp/${PRJ}.bin"

${BINDIR}/${PRJ}.bin: ${BINDIR}/${PRJ}.asc
	icepack ${BINDIR}/${PRJ}.asc ${BINDIR}/${PRJ}.bin

${BINDIR}/${PRJ}.asc: ${BINDIR}/${PRJ}.json
	nextpnr-${FPGA_FAMILY} --${FPGA_MODEL} --package ${FPGA_PACKAGE} --json ${BINDIR}/${PRJ}.json --pcf ${SRCDIR}/constraints/pins.pcf --freq ${TARGET_FREQ_MHZ} --asc ${BINDIR}/${PRJ}.asc -r

${BINDIR}/${PRJ}.json: ${SRCFILES} Makefile
	yosys -f "verilog -sv" -p "synth_${FPGA_FAMILY} -top top -json ${BINDIR}/${PRJ}.json -blif ${BINDIR}/${PRJ}.blif" ${SRCFILES}

