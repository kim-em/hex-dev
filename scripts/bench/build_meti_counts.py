#!/usr/bin/env python3
"""Build an isolated counts-only executable from the actual Phase-4 producer.

Generated C and the ordinary Lake binary stay unchanged. Compiler recipes,
every object/archive input, injected workers and both executables are bound
by digests. These counters do not provide scientific timing observations.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.build_nested_normalization_counts import digest, recipe
from scripts.bench.meti_counts import KINDS, instrument


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    root = Path.cwd().resolve()
    output = args.output.resolve()
    if output == root or root in output.parents:
        raise ValueError('diagnostic output must be outside the checkout')
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        raise ValueError('observer requires the pinned Lean 4.35.0-rc3 ABI')
    if subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip():
        raise ValueError('counter builds require a clean source tree')
    build = ['lake', 'build', 'hexrealclosure_phase4']
    subprocess.run(build, check=True)
    subprocess.run(['lake', 'build', '--no-build', 'hexrealclosure_phase4'], check=True)
    if subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip():
        raise ValueError('source tree changed during the build')
    output.mkdir(parents=True, exist_ok=False)
    executable = root / '.lake/build/bin/hexrealclosure_phase4'
    rsp = executable.with_suffix('.rsp')
    arguments = shlex.split(rsp.read_text())
    inputs = {str(Path(arg).resolve()): digest(Path(arg)) for arg in arguments
              if Path(arg).is_file() and arg.endswith(('.o.export', '.o', '.a'))}
    metadata = dict(
        schema=1, source_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        purpose='operation counts only; no timing or complexity verdict',
        builder_sha256=digest(Path(__file__)),
        selector_sha256=digest(root / 'scripts/bench/meti_counts.py'),
        recipe_reader_sha256=digest(root / 'scripts/bench/build_nested_normalization_counts.py'),
        ordinary_binary_sha256=digest(executable), rsp_sha256=digest(rsp),
        toolchain_sha256=digest(root / 'lean-toolchain'),
        lake_manifest_sha256=digest(root / 'lake-manifest.json'),
        lakefile_sha256=digest(root / 'lakefile.lean'),
        kinds=list(KINDS), objects=[], link_inputs=inputs, commands=[build])

    def run(command):
        metadata['commands'].append(command)
        subprocess.run(command, check=True)

    for index, argument in enumerate(arguments):
        if not argument.endswith('.c.o.export') or not Path(argument).is_file():
            continue
        original = Path(argument.removesuffix('.o.export'))
        changed, functions = instrument(original.read_text())
        if not functions:
            continue
        copied = output / f'{index}.c'
        target = output / f'{index}.o'
        copied.write_text(changed)
        command = recipe(Path(argument + '.trace'))
        command[command.index('-o') + 1] = str(target)
        sources = [i for i, arg in enumerate(command) if arg.endswith('.c')]
        if len(sources) != 1:
            raise ValueError('expected one generated C source in compiler recipe')
        command[sources[0]] = str(copied)
        run(command)
        arguments[index] = str(target)
        metadata['objects'].append(dict(
            input=str(original.resolve()), input_sha256=digest(original),
            observer_c=str(copied), observer_c_sha256=digest(copied),
            observer_object_sha256=digest(target), functions=functions))
    available = {f['kind'] for obj in metadata['objects'] for f in obj['functions']}
    required = {'poly_gcd', 'gcd_loop_tests', 'yun_loop_tests', 'chain_loop_tests',
                'signed_chains', 'bisection_nodes', 'bkr_solves'}
    if not required <= available:
        raise ValueError(f'missing generated workers: {sorted(required - available)}')
    metadata['instrumented_kinds'] = sorted(available)

    labels = output / 'labels.h'
    labels.write_text('#define HEX_METI_KINDS ' + ','.join(map(json.dumps, KINDS)) + '\n')
    observer = root / 'scripts/bench/ffi/meti_counts.c'
    observer_object = output / 'observer.o'
    example = recipe(root / '.lake/build/ir/HexRealClosure/Phase4.c.o.export.trace')
    include = example[example.index('-I') + 1]
    host_cc = shutil.which('cc')
    if host_cc is None:
        raise ValueError('host C compiler unavailable')
    metadata['observer_compiler_version'] = subprocess.check_output([host_cc, '--version'], text=True)
    run([host_cc, '-c', '-o', str(observer_object), str(observer), '-include', str(labels),
         '-I', include, '-fPIC', '-O3', '-std=c11'])
    arguments.append(str(observer_object))
    for symbol in ['lean_nat_gcd', '__gmpz_gcd', '__gmpz_gcdext', 'lean_io_prim_handle_put_str']:
        arguments.append('-Wl,--wrap=' + symbol)
    for path, checksum in inputs.items():
        if digest(Path(path)) != checksum:
            raise ValueError(f'original link input changed: {path}')
    binary = output / 'metitarski-counts'
    compiler = recipe(executable.with_suffix('.trace'))[0]
    run([compiler, '-o', str(binary)] + arguments)
    if digest(executable) != metadata['ordinary_binary_sha256']:
        raise ValueError('ordinary executable changed during the diagnostic build')
    for path, checksum in inputs.items():
        if digest(Path(path)) != checksum:
            raise ValueError(f'original link input changed during linking: {path}')
    if (subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip() or
            subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() !=
            metadata['source_head'] or digest(rsp) != metadata['rsp_sha256']):
        raise ValueError('source or link recipe changed during the diagnostic build')
    metadata.update(observer_sha256=digest(observer), labels_sha256=digest(labels),
                    observer_object_sha256=digest(observer_object),
                    diagnostic_binary_sha256=digest(binary), status='completed')
    (output / 'build.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(binary)


if __name__ == '__main__':
    main()
