"""Check retained compiler recipes against the exact diagnostic commands.

Recipe supplements are collected after the run from matching build outputs;
they do not retroactively freeze the compiler wrapper or system libraries.
"""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path
import shlex
import subprocess

WRAPS = ['lean_nat_gcd', '__gmpz_gcd', '__gmpz_gcdext', 'lean_io_prim_handle_put_str']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def command(trace):
    commands = [row['message'][3:] for row in trace['log'] if row['message'].startswith('.> ')]
    require(len(commands) == 1, 'expected one retained compiler recipe')
    return shlex.split(commands[0])


def validate(record, build, recipes):
    require(recipes['schema'] == 1 and recipes['source'] == record['commit'] and
            recipes['collection'] == 'post-capture matching build outputs', 'changed recipe provenance')
    require(sha(recipes['link_rsp'].encode()) == build['rsp_sha256'], 'changed original link response')
    require(recipes['verified_link_inputs'] == build['link_inputs'], 'changed recipe object identities')
    for key, name in [('toolchain_sha256', 'lean-toolchain'),
                      ('lake_manifest_sha256', 'lake-manifest.json'), ('lakefile_sha256', 'lakefile.lean')]:
        require(sha(recipes['sources'][name].encode()) == build[key], 'changed build configuration')
    require(recipes['sources']['lean-toolchain'].strip() == 'leanprover/lean4:v4.35.0-rc3',
            'changed pinned toolchain')
    require(build['commands'][0] == ['lake', 'build', 'hexrealclosure_phase4'], 'changed build command')
    original_link = command(recipes['link_trace'])
    require(len(original_link) == 4 and original_link[1] == '-o' and
            original_link[3] == '@' + original_link[2] + '.rsp', 'changed original linker recipe')
    checkout = Path(original_link[2]).parents[3]
    require(original_link[2] == str(checkout / '.lake/build/bin/hexrealclosure_phase4'),
            'changed original linker output')
    replacements = {}
    require(set(recipes['module_traces']) == {obj['input'] for obj in build['objects']},
            'changed module recipe inventory')
    for i, obj in enumerate(build['objects']):
        original = command(recipes['module_traces'][obj['input']])
        source = [j for j, arg in enumerate(original) if arg.endswith('.c')]
        require(len(source) == 1, 'changed original compiler source inventory')
        original_source = original[source[0]]
        require(obj['input'].startswith(str(checkout / '.lake/build/ir') + '/') and
                original_source.endswith('/' + str(Path(obj['input']).relative_to(checkout))) and
                original[original.index('-o') + 1] == original_source + '.o.export',
                'changed original module recipe binding')
        target = str(Path(obj['observer_c']).with_suffix('.o'))
        original[original.index('-o') + 1] = target
        original[source[0]] = obj['observer_c']
        require(original == build['commands'][i + 1], 'changed module compiler recipe')
        replacements[obj['input'] + '.o.export'] = target
    destination = Path(record['commands'][4]['argv'][2])
    binary = str(destination / 'metitarski-counts')
    observer = str(destination / 'observer.o')
    arguments = [replacements.get(arg, arg) for arg in shlex.split(recipes['link_rsp'])]
    require(build['commands'][-1] == [original_link[0], '-o', binary] + arguments +
            [observer] + ['-Wl,--wrap=' + symbol for symbol in WRAPS], 'changed ordered linker recipe')
    phase4 = command(recipes['phase4_trace'])
    phase4_source = str(checkout / '.lake/build/ir/HexRealClosure/Phase4.c')
    require([arg for arg in phase4 if arg.endswith('.c')] == [phase4_source] and
            phase4[phase4.index('-o') + 1] == phase4_source + '.o.export',
            'changed Phase4 compiler recipe binding')
    include = phase4[phase4.index('-I') + 1]
    observer_command = build['commands'][-2]
    require(Path(recipes['observer_cc']).name == 'cc' and
            observer_command == [recipes['observer_cc'], '-c', '-o', observer,
            str(checkout / 'scripts/bench/ffi/meti_counts.c'), '-include', str(destination / 'labels.h'),
            '-I', include, '-fPIC', '-O3', '-std=c11'], 'changed observer compiler recipe')


def collect(capture, checkout):
    record = json.loads((capture / 'manifest.json').read_text())
    build = json.loads((capture / 'build/build.json').read_text())
    # Recheck every original linked object before calling these matching outputs.
    for path, checksum in build['link_inputs'].items():
        require(sha(Path(path).read_bytes()) == checksum, 'original link input changed: ' + path)
    executable = checkout / '.lake/build/bin/hexrealclosure_phase4'
    require(sha(executable.read_bytes()) == build['ordinary_binary_sha256'], 'original binary changed')
    result = dict(schema=1, source=record['commit'], collection='post-capture matching build outputs',
                  collected_utc=datetime.now(timezone.utc).isoformat(),
                  collection_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip(),
                  collection_dirty=bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=checkout, text=True).strip()),
                  link_rsp=executable.with_suffix('.rsp').read_text(),
                  link_trace=json.loads(executable.with_suffix('.trace').read_text()),
                  phase4_trace=json.loads((checkout / '.lake/build/ir/HexRealClosure/Phase4.c.o.export.trace').read_text()),
                  module_traces={obj['input']: json.loads(Path(obj['input'] + '.o.export.trace').read_text())
                                 for obj in build['objects']},
                  sources={name: (checkout / name).read_text() for name in
                           ['lean-toolchain', 'lake-manifest.json', 'lakefile.lean']},
                  observer_cc=build['commands'][-2][0], verified_link_inputs=build['link_inputs'])
    validate(record, build, result)
    return result
