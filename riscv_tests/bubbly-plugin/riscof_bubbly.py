import os
import re
import shutil
import subprocess
import shlex
import logging
import random
import string
from string import Template
import sys
import glob

import riscof.utils as utils
import riscof.constants as constants
from riscof.pluginTemplate import pluginTemplate

logger = logging.getLogger()

# Output a wave.wlf for each test.
# This will slow down simulation considerably.
SAVE_WAVEFORM = 0

class bubbly(pluginTemplate):
    __model__ = "bubbly"
    __version__ = "0.1"

    def __init__(self, *args, **kwargs):
        sclass = super().__init__(*args, **kwargs)

        config = kwargs.get('config')

        # If the config node for this DUT is missing or empty. Raise an error. At minimum we need
        # the paths to the ispec and pspec files
        if config is None:
            print("Please enter input file paths in configuration.")
            raise SystemExit(1)

        # In case of an RTL based DUT, this would be point to the final binary executable of your
        # test-bench produced by a simulator (like verilator, vcs, incisive, etc).
        questa_bin_path =  os.environ['QUESTA_BIN'] if 'QUESTA_BIN' in os.environ else ""
        self.vlog_exe = os.path.join(questa_bin_path, "vlog")
        self.vopt_exe = os.path.join(questa_bin_path, "vopt")
        self.vsim_exe = os.path.join(questa_bin_path, "vsim")

        # Number of parallel jobs that can be spawned off by RISCOF
        # for various actions performed in later functions, specifically to run the tests in
        # parallel on the DUT executable. Can also be used in the build function if required.
        self.num_jobs = str(config['jobs'] if 'jobs' in config else 1)

        # Path to the directory where this python file is located. Collect it from the config.ini
        self.pluginpath=os.path.abspath(config['pluginpath'])

        # Collect the paths to the  riscv-config absed ISA and platform yaml files. One can choose
        # to hardcode these here itself instead of picking it from the config.ini file.
        self.isa_spec = os.path.abspath(config['ispec'])
        self.platform_spec = os.path.abspath(config['pspec'])

        #We capture if the user would like the run the tests on the target or
        #not. If you are interested in just compiling the tests and not running
        #them on the target, then following variable should be set to False
        if 'target_run' in config and config['target_run']=='0':
            self.target_run = False
        else:
            self.target_run = True

        # Return the parameters set above back to RISCOF for further processing.
        return sclass

    def initialise(self, suite, work_dir, archtest_env):
        # capture the working directory. Any artifacts that the DUT creates should be placed in this
        # directory. Other artifacts from the framework and the Reference plugin will also be placed
        # here itself.
        self.work_dir = work_dir
        self.questa_work_dir = os.path.abspath(os.path.join(work_dir, "questa_work"))

        self.src_dir = os.path.abspath(os.path.join(self.pluginpath, '../../src/'))
        self.test_dir = os.path.abspath(os.path.join(self.pluginpath, '../../test/'))
        self.tb_name = 'riscv_arch_test_tb'
        self.tb_path = os.path.abspath(os.path.join(self.pluginpath, f"{self.tb_name}.sv"))

        # capture the architectural test-suite directory.
        self.suite_dir = suite

        # Note the march is not hardwired here, because it will change for each
        # test. Similarly the output elf name and compile macros will be assigned later in the
        # runTests function
        self.compile_cmd = 'riscv{1}-unknown-elf-gcc -march={0} \
         -static -mcmodel=medany -fvisibility=hidden -nostdlib -nostartfiles -g\
         -T '+self.pluginpath+'/env/link.ld\
         -I '+self.pluginpath+'/env/\
         -I ' + archtest_env + ' {2} -o {3} {4}'

        # add more utility snippets here

    def build(self, isa_yaml, platform_yaml):
        # load the isa yaml as a dictionary in python.
        ispec = utils.load_yaml(isa_yaml)['hart0']

        # capture the XLEN value by picking the max value in 'supported_xlen' field of isa yaml. This
        # will be useful in setting integer value in the compiler string (if not already hardcoded);
        self.xlen = ('64' if 64 in ispec['supported_xlen'] else '32')

        # start building the '--isa' argument. the self.isa is dutnmae specific and may not be
        # useful for all DUTs
        self.isa = 'rv' + self.xlen
        if "I" in ispec["ISA"]:
            self.isa += 'i'
        if "M" in ispec["ISA"]:
            self.isa += 'm'
        if "F" in ispec["ISA"]:
            self.isa += 'f'
        if "D" in ispec["ISA"]:
            self.isa += 'd'
        if "C" in ispec["ISA"]:
            self.isa += 'c'
        # We only support Zbb and Zbs at the moment
        # (We're also not allowed to have B in the YAML ispec["ISA"] at the moment, so this is hardcoded)
        self.isa += 'b'

        # The following assumes we are using the riscv-gcc toolchain.
        self.compile_cmd = self.compile_cmd+' -mabi='+('lp64 ' if 64 in ispec['supported_xlen'] else 'ilp32 ')

        self.vlog_args = ["-work", self.questa_work_dir, "-sv", f"+incdir+{self.src_dir}", "-quiet", "-O5"]
        self.vopt_args = ["-work", self.questa_work_dir, "-quiet", "-O5", "+floatparameters"]
        if SAVE_WAVEFORM:
            self.vopt_args += ["+acc"]

        src_files_unordered = (glob.glob(self.src_dir+'/**/*.v', recursive=True) +
                               glob.glob(self.src_dir+'/**/*.sv', recursive=True) +
                               glob.glob(self.src_dir+'/**/*.svh', recursive=True))
        src_files_str = subprocess.check_output(['sv_auto_order', '-i', self.src_dir] + src_files_unordered).decode()
        self.src_files = src_files_str.split(' ')

        testbenches = (glob.glob(self.test_dir+'/**/*_tb.v', recursive=True) +
                            glob.glob(self.test_dir+'/**/*_tb.sv', recursive=True))
        test_files = (glob.glob(self.test_dir+'/**/*.v', recursive=True) +
                      glob.glob(self.test_dir+'/**/*.sv', recursive=True))
        self.test_src = [f for f in test_files if f not in testbenches]



    def runTests(self, testList):
        # Delete Makefile if it already exists.
        if os.path.exists(self.work_dir+ "/Makefile." + self.name[:-1]):
            os.remove(self.work_dir+ "/Makefile." + self.name[:-1])
        # create an instance the makeUtil class that we will use to create targets.
        make = utils.makeUtil(makefilePath=os.path.join(self.work_dir, "Makefile." + self.name[:-1]))

        # set the make command that will be used. The num_jobs parameter was set in the __init__
        # function earlier
        make.makeCommand = 'make -j' + self.num_jobs

        # We could prebuild all the non-testbench verilog source files, these are the same for each test
        # ... but unfortunately we're in a separate directory for each test file, so annoying to reuse this library
        subprocess.run([self.vlog_exe, *self.vlog_args, *self.src_files, *self.test_src, self.tb_path], check=True)
        subprocess.run([self.vopt_exe, *self.vopt_args, self.tb_name, "-o", self.tb_name+"_opt"], check=True)

        # we will iterate over each entry in the testList. Each entry node will be refered to by the
        # variable testname.
        for testname in testList:

            # for each testname we get all its fields (as described by the testList format)
            testentry = testList[testname]

            # we capture the path to the assembly file of this test
            test = testentry['test_path']

            # capture the directory where the artifacts of this test will be dumped/created. RISCOF is
            # going to look into this directory for the signature files
            test_dir = testentry['work_dir']

            # name of the elf file after compilation of the test
            elf = 'my.elf'

            # name of the signature file as per requirement of RISCOF. RISCOF expects the signature to
            # be named as DUT-<dut-name>.signature. The below variable creates an absolute path of
            # signature file.
            sig_file = os.path.join(test_dir, self.name[:-1] + ".signature")
            sig_file_name = os.path.basename(sig_file)

            # for each test there are specific compile macros that need to be enabled. The macros in
            # the testList node only contain the macros/values. For the gcc toolchain we need to
            # prefix with "-D". The following does precisely that.
            compile_macros= ' -D' + " -D".join(testentry['macros'])

            # substitute all variables in the compile command that we created in the initialize
            # function
            c_compile_cmd = self.compile_cmd.format(testentry['isa'].lower(), self.xlen, test, elf, compile_macros)

            load_elf_cmd = f"{os.path.join(self.pluginpath, 'load_elf.py')}"

            # We need $$ to make it a bash expansion, not a make expansion (which are all resolved way too eagerly!)
            loaded_bin_path = os.path.abspath(os.path.join(test_dir, 'loaded_elf.bin'))
            elf_path = os.path.abspath(os.path.join(test_dir, elf))
            loaded_bin_size_cmd = f"$$(stat -L -c %s {loaded_bin_path})"
            sig_start_cmd = f"$$(nm {elf_path} | grep begin_signature | awk '{{ print strtonum(\"0x\"$$1) }}')"
            sig_end_cmd = f"$$(nm {elf_path} | grep end_signature | awk '{{ print strtonum(\"0x\"$$1) }}')"

            verilog_params = (f"-gINPUT_FILE=loaded_elf.bin -gOUTPUT_SIG_FILE={sig_file_name} "
                              f"-gBIN_SIZE={loaded_bin_size_cmd} "
                              f"-gSIG_START_VADDR={sig_start_cmd} -gSIG_END_VADDR={sig_end_cmd}")

            vsim_save_wave = "-wlf wave.wlf" if SAVE_WAVEFORM else ""
            vsim_do_wave = "add wave -r /*; " if SAVE_WAVEFORM else ""
            vsim_do = f"-do \"{vsim_do_wave}run -all\""

            # if the user wants to disable running the tests and only compile the tests, then
            # the "else" clause is executed below assigning the sim command to simple no action
            # echo statement.
            if self.target_run:
                # set up the simulation command. Template is for spike. Please change.
                vsim_cmd = f"{self.vsim_exe} -c -lib {self.questa_work_dir} {verilog_params} {vsim_save_wave} {self.tb_name}_opt {vsim_do}"
            else:
                vsim_cmd = 'echo "NO RUN"'

            # concatenate all commands that need to be executed within a make-target.
            execute = '@cd {0}; {1}; {2}; {3};'.format(testentry['work_dir'], c_compile_cmd, load_elf_cmd, vsim_cmd)

            # create a target. The makeutil will create a target with the name "TARGET<num>" where num
            # starts from 0 and increments automatically for each new target that is added
            make.add_target(execute)

        # if you would like to exit the framework once the makefile generation is complete uncomment the
        # following line. Note this will prevent any signature checking or report generation.
        #raise SystemExit

        # once the make-targets are done and the makefile has been created, run all the targets in
        # parallel using the make command set above.
        make.execute_all(self.work_dir)

        # if target runs are not required then we simply exit as this point after running all
        # the makefile targets.
        if not self.target_run:
            raise SystemExit(0)
