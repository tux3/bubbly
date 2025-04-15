.PHONY: setup_uv riscof_tests update_arch_tests clean mrproper

all: riscof_tests

setup_uv: pyproject.toml
	uv sync

# NOTE: This one isn't .PHONY, it clones the git directory riscv-arch-test
riscv-arch-test: setup_uv
	uv run -- riscof --verbose info arch-test --clone

update_arch_tests: setup_uv
	uv run -- riscof --verbose info arch-test --update

riscof_tests: setup_uv riscv-arch-test
	uv run -- riscof --verbose info run --config=config.ini --suite=riscv-arch-test/riscv-test-suite/ --env=riscv-arch-test/riscv-test-suite/env

clean:
	rm -rf riscof_work

mrproper: clean
	rm -rf riscv-arch-test uv.lock .venv
