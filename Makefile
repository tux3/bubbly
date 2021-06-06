FPGA_FAMILY=ice40
FPGA_MODEL=lp8k
FPGA_PACKAGE=cm81

TARGET_FREQ_MHZ=32

SRCDIR=./src
BINDIR=./build
PRJ=$(notdir ${PWD})
AVHDL_PRJ_DIR=./project/${PRJ}/aldec/${PRJ}
AVHDL_OPTS=-work ${PRJ} -dbg -sve -msg 5 -sv2k12
AVHDL_LOG=${PWD}/${BINDIR}/avhdl_test_output.log
AVHDL_SIM_OPTS=-O5 -L ice -l ${AVHDL_LOG} +access +w_nets +accb +accr +access +r +access +r+w

SV_AUTO_ORDER_FAILED=//__SV_AUTO_ORDER_FAIL__// # Can't find a clean way to exit if a $shell command fails, so use a marker error value
SRCFILES_UNORDERED=$(filter-out $(shell find ${SRCDIR}/test/ -name *.v -or -name *.sv) $(shell find ${SRCDIR}/board/arty/ -name *.sv), $(shell find ${SRCDIR} -name *.v -or -name *.sv -or -name *.svh))
test: TESTBENCHES=$(filter-out $(shell find ${PWD}/${SRCDIR}/test/post_synth/ -type f), $(shell find ${PWD}/${SRCDIR}/test/ -name *_tb.v -or -name *_tb.sv))
test: TESTSRC=$(shell sv_auto_order --absolute $(filter-out $(shell find ${PWD}/${SRCDIR}/test/ -name *_tb.v -or -name *_tb.sv), $(shell find ${PWD}/${SRCDIR}/test/ -name *.v -or -name *.sv)))
test: SRCFILES=$(shell sv_auto_order --absolute ${SRCFILES_UNORDERED})
${BINDIR}/${PRJ}.json: SRCFILES=$(shell sv_auto_order ${SRCFILES_UNORDERED})

all: ${BINDIR}/${PRJ}.bin
	

clean:
	rm -f $(wildcard ${BINDIR}/${PRJ}.*)

mrproper: clean
	rm -f ./${AVHDL_PRJ_DIR}/${PRJ}/*.mgf
	rm -rf ./${AVHDL_PRJ_DIR}/${PRJ}/slp/*

flash: ${BINDIR}/${PRJ}.bin
	rsync -avzh "$^" "pi:/tmp/${PRJ}.bin"
	ssh pi tinyprog -p "/tmp/${PRJ}.bin"

${BINDIR}/${PRJ}.bin: ${BINDIR}/${PRJ}.asc
	icepack ${BINDIR}/${PRJ}.asc ${BINDIR}/${PRJ}.bin

${BINDIR}/${PRJ}.asc: ${BINDIR}/${PRJ}.json
	nextpnr-${FPGA_FAMILY} --${FPGA_MODEL} --package ${FPGA_PACKAGE} --json ${BINDIR}/${PRJ}.json --pcf ${SRCDIR}/board/ice40/pins.pcf --freq ${TARGET_FREQ_MHZ} --asc ${BINDIR}/${PRJ}.asc -r

${BINDIR}/${PRJ}.json: ${SRCFILES_UNORDERED} Makefile
	@test "${SRCFILES}"
	yosys -f "verilog -sv" -p "synth_${FPGA_FAMILY} -top top -json ${BINDIR}/${PRJ}.json -blif ${BINDIR}/${PRJ}.blif" ${SRCFILES}

test:
	@# If either is undefined then sv_auto_order must have failed, most likely due to a parse error
	@test "${SRCFILES}"
	@test "${TESTSRC}"

	@echo "# Compiling sources"
	@cd ${AVHDL_PRJ_DIR} && wine ${AVHDL_BIN}/vlog.exe ${AVHDL_OPTS} ${SRCFILES} ${TESTSRC} | tee ${AVHDL_LOG}
	@if grep -q "Compile failure" ${AVHDL_LOG}; then echo "# Failed to compile, giving up!"; exit 1; fi
	@$(foreach tb, ${TESTBENCHES}, \
		echo "# Compiling testbench $(basename $(notdir ${tb})) " \
		&& cd ${PWD}/${AVHDL_PRJ_DIR} && wine ${AVHDL_BIN}/vlog.exe ${AVHDL_OPTS} ${tb} | tee ${AVHDL_LOG} \
		; if grep -q "Compile failure" ${AVHDL_LOG}; then echo "# Failed to compile, giving up!"; exit 1; fi \
		; echo "# Running testbench $(basename $(notdir ${tb})) " \
		; : > ${AVHDL_LOG} \
		&& cd ${PWD}/${AVHDL_PRJ_DIR} && wine ${AVHDL_BIN}/vsim.exe -c -lib ${PRJ} ${AVHDL_SIM_OPTS} $(basename $(notdir ${tb})) -do "run -all" \
				| ack --color --color-match="black on_red" --passthru "KERNEL: (Fatal )?Error:" \
		; if ! grep -q "KERNEL: Kernel process initialization done." ${AVHDL_LOG}; then echo "# Failed to understand simulation log file, giving up!"; exit 1; fi \
		&& if grep -q -E "KERNEL: (Fatal )?Error:" ${AVHDL_LOG}; then echo "# Testbench ${tb} failed with errors!"; exit 1; fi \
	;)
