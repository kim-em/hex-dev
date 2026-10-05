#!/usr/bin/env python3
"""Build an isolated diagnostic binary from Lake's generated C and link recipe.

Every selected polynomial-gcd entry receives one observer call before its
unchanged body. Generic argument/boxing forwarders are excluded, so the
actual worker is counted once. Inlining retains the side effect. All injected
functions and generated-C digests are recorded. Integer gcd counters wrap
actual Lean/GMP symbols; these are separate layers and must not be summed.
This binary is for counts only: timings must use the unmodified Lake binary.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess

KINDS = {'gcd': 0, 'xgcd': 1, 'xgcdLeft': 2, 'pseudoGcd': 3}
ENTRY = re.compile(r'^LEAN_EXPORT [^;\n{}]*\b(\w+)\([^\n;]*\)\{', re.M)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def instrument(source):
    insertions = []
    names = []
    for match in ENTRY.finditer(source):
        name = match.group(1)
        # Specialization suffixes name callees too. Classify the first
        # declaration name, never a later '...___at___...DensePoly_gcd...'.
        declaration, *specialization = name.split('___at___', 1)
        if specialization and re.search(r'_spec__\d+(?:___redArg)?$', specialization[0]) is None:
            continue
        if '_DensePoly_' not in declaration:
            continue
        operation = declaration.split('_DensePoly_', 1)[1]
        kind = operation.split('___', 1)[0]
        if kind not in KINDS or operation not in (kind, kind + '___redArg'):
            continue
        # Read the entire generated function, ignoring strings and comments.
        remainder = source[match.end():]
        braces = 1
        end = None
        for token in re.finditer(r'"(?:\\.|[^"\\])*"|/\*.*?\*/|//[^\n]*|[{}]', remainder, re.S):
            if token.group() == '{': braces += 1
            if token.group() == '}': braces -= 1
            if braces == 0:
                end = token.end()
                break
        if end is None:
            raise ValueError(f'unterminated generated function: {name}')
        body = remainder[:end]
        # The full generic arity forwards to the redArg worker. Instrument
        # the worker, rather than adding a second count at its forwarder.
        if not name.endswith('___redArg') and name + '___redArg(' in body:
            continue
        insertions.append((match.end(), f'\nhex_nested_poly_count({KINDS[kind]});'))
        names.append(dict(name=name, kind=kind))
    for position, text in reversed(insertions):
        source = source[:position] + text + source[position:]
    if names:
        source = 'extern void hex_nested_poly_count(unsigned);\n' + source
    return source, names


def recipe(trace):
    rows = json.loads(trace.read_text())['log']
    commands = [row['message'][3:] for row in rows if row['message'].startswith('.> ')]
    if len(commands) != 1:
        raise ValueError(f'expected one Lake compiler recipe: {trace}')
    return shlex.split(commands[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    root = Path.cwd().resolve()
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.35.0-rc3':
        raise ValueError('observer calling convention requires Lean 4.35.0-rc3')
    if subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip():
        raise ValueError('counter builds require a clean source tree')
    build_command = ['lake', 'build', 'hexrealclosure_nested_normalization']
    subprocess.run(build_command, check=True)
    subprocess.run(['lake', 'build', '--no-build', 'hexrealclosure_nested_normalization'], check=True)
    if subprocess.check_output(['git', 'status', '--porcelain'], text=True).strip():
        raise ValueError('source tree changed during native target build')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    executable = root / '.lake/build/bin/hexrealclosure_nested_normalization'
    rsp = executable.with_suffix('.rsp')
    arguments = shlex.split(rsp.read_text())
    metadata = dict(source_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                    ordinary_binary_sha256=digest(executable), rsp_sha256=digest(rsp),
                    toolchain=(root / 'lean-toolchain').read_text().strip(),
                    toolchain_sha256=digest(root / 'lean-toolchain'),
                    lake_manifest_sha256=digest(root / 'lake-manifest.json'),
                    lakefile_sha256=digest(root / 'lakefile.lean'),
                    purpose='diagnostic counters only, not timing', objects=[], commands=[build_command],
                    link_inputs={str(Path(arg).resolve()): digest(Path(arg))
                                 for arg in arguments if Path(arg).is_file() and
                                 (arg.endswith('.o.export') or arg.endswith('.o') or arg.endswith('.a'))})

    def run(command):
        metadata['commands'].append(command)
        subprocess.run(command, check=True)

    for index, argument in enumerate(arguments):
        original_object = Path(argument)
        if not argument.endswith('.c.o.export') or not original_object.is_file():
            continue
        original_c = Path(argument.removesuffix('.o.export'))
        source = original_c.read_text()
        modified, names = instrument(source)
        if not names:
            continue
        copied = output / f'{index}.c'
        copied.write_text(modified)
        target = output / f'{index}.o'
        command = recipe(Path(argument + '.trace'))
        command[command.index('-o') + 1] = str(target)
        # Restored Lake traces can name a previous worktree. Replace the
        # single C input, using current generated bytes rather than that path.
        inputs = [i for i, arg in enumerate(command) if arg.endswith('.c')]
        if len(inputs) != 1:
            raise ValueError(f'expected one generated C input: {command}')
        command[inputs[0]] = str(copied)
        run(command)
        arguments[index] = str(target)
        metadata['objects'].append(dict(input=str(original_c), input_sha256=digest(original_c),
                                        observer_c_sha256=digest(copied), functions=names))
    if not metadata['objects']:
        raise ValueError('no polynomial gcd workers found')
    compiler = recipe(executable.with_suffix('.trace'))[0]
    # Use the same toolchain include/sysroot options as one compiled object.
    example = recipe(Path(str(root / '.lake/build/ir/HexRealClosure/NestedNormalization.c.o.export') + '.trace'))
    include = example[example.index('-I') + 1]
    observer = root / 'scripts/bench/ffi/nested_normalization_counts.c'
    observer_object = output / 'observer.o'
    # Lean's C sysroot deliberately omits libc headers. The observer uses the
    # host C toolchain for stdio; generated Lean C keeps its original recipe.
    host_cc = shutil.which('cc')
    if not host_cc:
        raise ValueError('host C compiler is unavailable')
    metadata['observer_compiler_version'] = subprocess.check_output([host_cc, '--version'], text=True)
    run([host_cc, '-c', '-o', str(observer_object), str(observer),
         '-I', include, '-fPIC', '-O3', '-std=c11'])
    arguments.append(str(observer_object))
    for symbol in ['lean_nat_gcd', '__gmpz_gcd', '__gmpz_gcdext', 'lean_io_prim_handle_put_str', 'lean_dbg_trace']:
        arguments.append('-Wl,--wrap=' + symbol)
    binary = output / 'nested-normalization-counts'
    run([compiler, '-o', str(binary)] + arguments)
    metadata.update(observer_sha256=digest(observer), diagnostic_binary_sha256=digest(binary))
    (output / 'build.json').write_text(json.dumps(metadata, indent=2) + '\n')
    print(binary)


if __name__ == '__main__':
    main()
