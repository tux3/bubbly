#!/usr/bin/env python3
from edalize import *
import os
import glob
import subprocess

build_dir = 'build'
base_dir = os.getcwd()
os.makedirs(build_dir, exist_ok=True)
os.chdir(build_dir)
build_dir = os.getcwd()
base_dir = os.path.relpath(base_dir, build_dir)

def scan_files(path, file_type):
    path = os.path.join(base_dir, path)
    files = [f for f in glob.iglob(path, recursive=True) if os.path.isfile(f)]
    return [{'name': f, 'file_type': file_type} for f in files]

def auto_order(files):
    paths = [f['name'] for f in files]
    paths = subprocess.check_output(['sv_auto_order', '-i', '../src']+paths).decode().strip().split(' ')
    files = []
    for p in paths:
        f = {'name': p, 'file_type': 'systemVerilogSource'}
        if p.endswith('.svh'):
            f['is_include_file'] = True
            f['include_path'] = os.path.join(base_dir, 'src')
        files.append(f)
    return files

files = auto_order(scan_files('src/**', 'systemVerilogSource'))
test_files = scan_files('test/**', 'systemVerilogSource')
files += test_files

files += scan_files('board/arty/*.sv', 'systemVerilogSource')
files += scan_files('board/arty/*.xdc', 'xdc')

with open('test_sources.tcl', 'w+') as f:
    test_file_names = ' '.join([file['name'] for file in test_files])
    f.write('move_files -fileset sim_1 [get_files  {' + test_file_names + '}]')
files += [{'name': 'test_sources.tcl', 'file_type': 'tclSource'}]

tool = 'vivado'
tool_options = {
    'vivado': {
        'part': 'xc7a100tcsg324-1'
    }
}
parameters = {
}
edam = {
  'files'        : files,
  'name'         : 'bubbly',
  'parameters'   : parameters,
  'tool_options' : tool_options,
  'toplevel'     : 'top'
}


backend = get_edatool(tool)(edam=edam, work_root=build_dir)
backend.configure()
# backend.build()

