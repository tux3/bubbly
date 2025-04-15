.PHONY: setup_uv test clean mrproper

all: test

setup_uv: pyproject.toml
	uv sync

test: setup_uv
	cargo build --release
	uv run rust_tests.py --fail-fast -j4

clean:
	cargo clean
	rm -r work/

mrproper: clean
