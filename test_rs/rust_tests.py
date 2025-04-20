import argparse
import os
import re
import subprocess
import glob
import concurrent.futures
import threading
from pathlib import Path
from load_elf import load_elf
import colorama
from colorama import Fore, Back, Style

# Output a wave.wlf for each test.
# This will slow down simulation considerably.
SAVE_WAVEFORM = False

class Simulator:
    def __init__(self, work_dir, fail_fast):
        # If we run tests in parallel, this lets us know to stop when a test fails in the middle
        self.fail_fast = fail_fast
        self.stop_flag = False
        # Don't interleave test results output
        self.output_lock = threading.Lock()

        questa_bin_path =  os.environ['QUESTA_BIN'] if 'QUESTA_BIN' in os.environ else ""
        self.work_dir = work_dir
        self.vlog_exe = os.path.join(questa_bin_path, "vlog")
        self.vopt_exe = os.path.join(questa_bin_path, "vopt")
        self.vsim_exe = os.path.join(questa_bin_path, "vsim")

        self_path = os.path.dirname(os.path.abspath(__file__))
        self.src_dir = os.path.abspath(os.path.join(self_path, '../src/'))
        self.test_dir = os.path.abspath(os.path.join(self_path, '../test/'))
        self.tb_name = 'rust_test_tb'
        self.tb_path = os.path.abspath(os.path.join(self_path, f"{self.tb_name}.sv"))

        self.vlog_args = ["-work", self.work_dir, "-sv", f"+incdir+{self.src_dir}", "-quiet", "-O5"]
        self.vopt_args = ["-work", self.work_dir, "-quiet", "-O5", "+floatparameters"]
        if SAVE_WAVEFORM:
            self.vopt_args += ["+acc"]


    def prebuild_testbench(self):
        print('Pre-building testbench: ordering sources')
        src_files_unordered = (glob.glob(self.src_dir+'/**/*.v', recursive=True) +
                               glob.glob(self.src_dir+'/**/*.sv', recursive=True) +
                               glob.glob(self.src_dir+'/**/*.svh', recursive=True))
        src_files_str = subprocess.check_output(['sv_auto_order', '-i', self.src_dir] + src_files_unordered).decode()
        src_files = src_files_str.split(' ')

        testbenches = (glob.glob(self.test_dir+'/**/*_tb.v', recursive=True) +
                       glob.glob(self.test_dir+'/**/*_tb.sv', recursive=True))
        test_files = (glob.glob(self.test_dir+'/**/*.v', recursive=True) +
                      glob.glob(self.test_dir+'/**/*.sv', recursive=True))
        test_src = [f for f in test_files if f not in testbenches]

        print('Pre-building testbench: compiling sources')
        subprocess.run([self.vlog_exe, *self.vlog_args, *src_files, *test_src, self.tb_path], check=True)
        print('Pre-building testbench: optimizing library')
        subprocess.run([self.vopt_exe, *self.vopt_args, self.tb_name, "-o", self.tb_name+"_opt"], check=True)


    def print_log_results(self, log_file, test_name):
        """
        Check the simulation log file for errors and warnings.
        If errors or warnings are found, display the entire log with color highlighting.
        """
        has_warnings = False
        has_errors = False
        has_completed = False
        log_lines = []

        with open(log_file, 'r') as f:
            for line in f:
                log_lines.append(line.rstrip())
                if "** Warning:" in line:
                    has_warnings = True
                if "** Error:" in line:
                    has_errors = True
                if re.search(r"# End time: .* on .*, Elapsed time: .*", line):
                    has_completed = True

        with self.output_lock:
            if not has_completed:
                for line in log_lines:
                    print(line)
                raise Exception(f"Incomplete simulation log for test {test_name}")

            if has_errors:
                print(f"{Style.BRIGHT}Test {test_name} failed:{Style.RESET_ALL}")
            elif has_warnings:
                print(f"{Style.BRIGHT}Test {test_name} passed with warnings:{Style.RESET_ALL}")
            else:
                print(f"{Style.BRIGHT}Test {test_name} passed{Style.RESET_ALL}")

            if has_warnings or has_errors:
                for line in log_lines:
                    if "** Warning:" in line:
                        print(f"{Fore.YELLOW}{line}{Style.RESET_ALL}")
                    elif "** Error:" in line:
                        print(f"{Back.RED}{Fore.BLACK}{line}{Style.RESET_ALL}")
                    else:
                        print(line)

            if has_errors and self.fail_fast:
                raise Exception(f"Test {test_name} failed")


    def run_test(self, test_elf_path):
        if self.fail_fast and self.stop_flag:
            return

        test_path = os.path.abspath(test_elf_path + '.bin')
        test_name = Path(test_path).stem
        #print(f"Running test: {test_name}")

        load_elf(test_elf_path, test_path)

        log_file = os.path.join(self.work_dir, f"transcript_{test_name}.log")
        vsim_save_wave = ["-wlf", f"{self.work_dir}/wave_{test_name}.wlf"] if SAVE_WAVEFORM else []
        vsim_do_wave = "add wave -r /*; " if SAVE_WAVEFORM else ""
        vsim_do = ["-do", f"{vsim_do_wave}run -all"]

        vsim_args = [
            self.vsim_exe,
            "-c",
            "-lib", self.work_dir,
            f"-gINPUT_FILE={test_path}",
            f"-gBIN_SIZE={os.path.getsize(test_path)}",
            f"{self.tb_name}_opt",
            "-quiet",
            "-nostdout",
            "-logfile", log_file,
            *vsim_save_wave,
            *vsim_do
        ]
        subprocess.run(vsim_args, check=True, stdout=subprocess.DEVNULL)

        # Futures get suspended on subprocess.run, if a previous test fails we likely wakeup here
        if self.fail_fast and self.stop_flag:
            return
        self.print_log_results(log_file, test_name)


def find_test_binaries():
    cargo_bin_dir = 'target/riscv64imac-unknown-none-elf/release/'
    test_files = []
    for file in os.listdir('./src/bin'):
        if not file.endswith('.rs'):
            continue
        test_name = Path(file).stem
        test_files.append(os.path.join(cargo_bin_dir, test_name))
    return test_files


def main(test_binaries, work_path, fail_fast, jobs=1):
    # Initialize colorama for cross-platform color support
    colorama.init()

    if not test_binaries:
        test_binaries = find_test_binaries()

    sim = Simulator(work_path, fail_fast)
    sim.prebuild_testbench()

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = [executor.submit(sim.run_test, elf_path) for elf_path in test_binaries]

        for future in concurrent.futures.as_completed(futures):
            if exception := future.exception():
                if sim.fail_fast:
                     sim.stop_flag = True
                print(f"{exception}")
                exit(1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog='rust_tests.py')
    parser.add_argument('-w', '--work', type=str, default='work', help='Simulation work dir')
    parser.add_argument('-j', '--jobs', type=int, default=1,
                        help='Number of parallel jobs to run. Default: 1')
    parser.add_argument('--fail-fast', action='store_true', dest='fail_fast', default=True,
                        help='Stop after first failure')
    parser.add_argument('--no-fail-fast', action='store_false', dest='fail_fast',
                        help="Don't stop after first failure")
    parser.add_argument('tests', nargs='*', help='Optional list of test binaries to run')
    args = parser.parse_args()
    main(args.tests, args.work, args.fail_fast, args.jobs)

