FPGA_FAMILY=ice40
FPGA_MODEL=lp8k
FPGA_PACKAGE=cm81

TARGET_FREQ_MHZ=32

SRCDIR=./src
TESTDIR=./test
BOARDDIR=./board
BINDIR=./build
PRJ=$(notdir ${PWD})
AVHDL_PRJ_DIR=./project/${PRJ}/aldec/${PRJ}
#AVHDL_OPTS=-work ${PRJ} -dbg -sve -msg 5 -sv2k12 +incdir+${PWD}/${SRCDIR}
AVHDL_OPTS=-work ${PRJ} -sv +incdir+${PWD}/${SRCDIR}
AVHDL_LOG=${PWD}/${BINDIR}/avhdl_test_output.log
AVHDL_SIM_OPTS=-l ${AVHDL_LOG} -wlf wave.wlf

QUESTA_PRJ_DIR=${PWD}/${BINDIR}/questa/${PRJ}/
QUESTA_LOG=${PWD}/${BINDIR}/questa_test_output.log
QUESTA_VLOG_ARGS = -work ${PRJ} -sv +incdir+${PWD}/${SRCDIR} -quiet
# If you need to debug, we're supposed to use "-access=r+foo_tb -access=r+foo_tb/something" to include signals
# Unfortunately the new QIS simulator doesn't support WLF waveforms (compressed), only horribly inefficient VCD
# Passing +acc will disable QIS (slowdown), and allow using WLF format (much faster/smaller)
QUESTA_VOPT_ARGS=-work ${PRJ} $(basename $(notdir ${tb})) -o $(basename $(notdir ${tb}))_opt -quiet
# Add -wlf wave.wlf to save a WLF waveform (requires QIS disabled, i.e. pass +acc to vopt)
QUESTA_SIM_ARGS = -l ${QUESTA_LOG} -quiet

# TODO: Add a variable to decide whether we should save a waveform or not
#  If set to false, we shouldn't do add wave -r /* in the vsim -do script, that might add overhead for no reason...

IMPL_RUN=impl_1

SV_AUTO_ORDER=sv_auto_order -i ${SRCDIR}
SV_AUTO_ORDER_FAILED=//__SV_AUTO_ORDER_FAIL__// # Can't find a clean way to exit if a $shell command fails, so use a marker error value
SRCFILES_UNORDERED=$(shell find ${SRCDIR} -name '*.v' -or -name '*.sv' -or -name '*.svh')
test: TESTBENCHES=$(filter-out $(shell find ${PWD}/${TESTDIR}/post_synth/ -type f), $(shell find ${PWD}/${TESTDIR}/ -name '*_tb.v' -or -name '*_tb.sv'))
test: TESTSRC=$(shell ${SV_AUTO_ORDER} --absolute $(filter-out $(shell find ${PWD}/${TESTDIR}/ -name '*_tb.v' -or -name '*_tb.sv'), $(shell find ${PWD}/${TESTDIR}/ -name '*.v' -or -name '*.sv')))
test: SRCFILES=$(shell ${SV_AUTO_ORDER} --absolute ${SRCFILES_UNORDERED})
${BINDIR}/${PRJ}.json: SRCFILES=$(shell ${SV_AUTO_ORDER} ${SRCFILES_UNORDERED})

.PHONY: test all clean mrproper vivado bitstream program

all: ${BINDIR}/${PRJ}.xpr


clean:
	rm -rf ${BINDIR}

mrproper: clean
	rm -f ./${AVHDL_PRJ_DIR}/${PRJ}/*.mgf
	rm -rf ./${AVHDL_PRJ_DIR}/${PRJ}/slp/*

flash: ${BINDIR}/${PRJ}.bin
	rsync -avzh "$^" "pi:/tmp/${PRJ}.bin"
	ssh pi tinyprog -p "/tmp/${PRJ}.bin"

${BINDIR}/${PRJ}.bin: ${BINDIR}/${PRJ}.asc
	icepack ${BINDIR}/${PRJ}.asc ${BINDIR}/${PRJ}.bin

${BINDIR}/${PRJ}.asc: ${BINDIR}/${PRJ}.json
	nextpnr-${FPGA_FAMILY} --${FPGA_MODEL} --package ${FPGA_PACKAGE} --json ${BINDIR}/${PRJ}.json --pcf ${BOARDDIR}/ice40/pins.pcf --freq ${TARGET_FREQ_MHZ} --asc ${BINDIR}/${PRJ}.asc -r

${BINDIR}/${PRJ}.json: ${SRCFILES_UNORDERED} Makefile
	@test "${SRCFILES}"
	yosys -f "verilog -sv -I ${SRCDIR}" -p "synth_${FPGA_FAMILY} -top top -json ${BINDIR}/${PRJ}.json -blif ${BINDIR}/${PRJ}.blif" ${SRCFILES}

${BINDIR}/${PRJ}.xpr: edalize_build.py
	./edalize_build.py
	make -C ${BINDIR} ${PRJ}.xpr

vivado: ${BINDIR}/${PRJ}.xpr


${BINDIR}/${PRJ}.runs/${IMPL_RUN}/top.bit: ${BINDIR}/${PRJ}.xpr ${SRCFILES_UNORDERED}
	./tools/build_bitstream.tcl ${BINDIR}/${PRJ}.xpr ${IMPL_RUN}

bitstream: ${BINDIR}/${PRJ}.runs/${IMPL_RUN}/top.bit


program: ${BINDIR}/${PRJ}.runs/${IMPL_RUN}/top.bit
	./tools/program_bitstream.tcl "$^"

test:
	@# If either is undefined then sv_auto_order must have failed, most likely due to a parse error
	@test "${SRCFILES}"
	@test "${TESTSRC}"

	@echo "# Compiling sources"
	@mkdir -p ${QUESTA_PRJ_DIR}
	@cd ${QUESTA_PRJ_DIR} && ${QUESTA_BIN}/vlog ${QUESTA_VLOG_ARGS} ${SRCFILES} ${TESTSRC} | tee ${QUESTA_LOG}
	@if grep -q "\*\* Error:" ${QUESTA_LOG}; then echo "# Failed to compile, giving up!"; exit 1; fi
	@$(foreach tb, ${TESTBENCHES}, \
		echo "# Compiling testbench $(basename $(notdir ${tb})) " \
		&& cd ${QUESTA_PRJ_DIR} \
		&& ${QUESTA_BIN}/vlog ${QUESTA_VLOG_ARGS} $(realpath ${tb}) | tee ${QUESTA_LOG} \
			| ack --color --color-match="black on_red" --flush --passthru "\*\* Error:" \
			| ack --color --color-match="yellow" --flush --passthru "\*\* Warning:" \
		; if grep -q "Compile failure" ${QUESTA_LOG}; then echo "# Failed to compile, giving up!"; exit 1; fi \
		; echo "# Running testbench $(basename $(notdir ${tb})) " \
		; : > ${QUESTA_LOG} \
		&& cd ${QUESTA_PRJ_DIR} \
		&& ${QUESTA_BIN}/vopt ${QUESTA_VOPT_ARGS} \
		&& ${QUESTA_BIN}/vsim -c -lib ${PRJ} ${QUESTA_SIM_ARGS} $(basename $(notdir ${tb}))_opt -do "add wave -r /*; run -all" \
				| ack --color --color-match="black on_red" --flush --passthru "\*\* Error:" \
				| ack --color --color-match="yellow" --flush --passthru "\*\* Warning:" \
		; if ! grep -q "# End time: .* on .*, Elapsed time: .*" ${QUESTA_LOG}; then echo "# Failed to understand simulation log file, giving up!"; exit 1; fi \
		&& if grep -q -E "KERNEL: (Fatal )?Error:" ${QUESTA_LOG}; then echo "# Testbench ${tb} failed with errors!"; exit 1; fi \
	;)
