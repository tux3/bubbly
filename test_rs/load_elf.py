#!/usr/bin/env python3

import argparse
import lief
import os

VERBOSE = False

# We're "loading" the ELF file in a single buffer that we can write to disk
# This buffer starts at the lowest address that we need to actually load
def base_virtual_addr(elf):
    base_addr = None
    for segment in elf.segments:
        if segment.type != lief.ELF.Segment.TYPE.LOAD:
            continue
        if segment.virtual_size == 0:
            continue
        if base_addr:
            base_addr = min(base_addr, segment.virtual_address)
        else:
            base_addr = segment.virtual_address
    return base_addr


def write_segment(file, base_vaddr, segment):
    if segment.type != lief.ELF.Segment.TYPE.LOAD:
        return
    if segment.virtual_size == 0:
        return
    load_offset = segment.virtual_address - base_vaddr
    if VERBOSE:
        print(
            f"Loading segment: Phys 0x{segment.physical_address:x} 0x{segment.physical_size:x}, Virt 0x{segment.virtual_address:x} 0x{segment.virtual_size:x}")
        print(f"Load offset: 0x{load_offset:x}, size 0x{len(segment.content):x}")
    assert len(segment.content) == segment.virtual_size

    file.seek(load_offset, os.SEEK_SET)
    file.write(segment.content)


def load_parsed_elf(elf, out_path):
    base_vaddr = base_virtual_addr(elf)
    if VERBOSE:
        print(f"OEP: 0x{elf.header.entrypoint:x}")
        print(f"Base vaddr: 0x{base_vaddr:x}")

    with open(out_path, "wb+") as file:
        for segment in elf.segments:
            write_segment(file, base_vaddr, segment)


def load_elf(input_path, output_path):
    elf = lief.ELF.parse(input_path)
    load_parsed_elf(elf, output_path)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(prog='load_elf.py')
    parser.add_argument('input')
    parser.add_argument('-o', '--output')
    args = parser.parse_args()
    load_elf(args.input, args.output)
