#!/usr/bin/env python3
"""Archive and verify the complete untimed MetiTarski counter diagnostic.

Keep every command log, packet, source snapshot and instrumented C file.
Omit only executable/object snapshots whose identities remain cross-bound to
the original capture and build metadata. Verification never executes a packet.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import sys
import tarfile

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench.meti_counts import KINDS, _distinct, check_packet, instrument, parse_record
from scripts.bench.real_closure_meti_counts import DEGREES, SOURCES
from scripts.bench.meti_recipes import validate as validate_recipes

ARCHIVE = Path('reports/bench-results/real-closure-metitarski-counts')
BEGIN, END = '<!-- meti-counts -->', '<!-- /meti-counts -->'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def document(data):
    return json.loads(data, object_pairs_hook=_distinct)


def relative(name):
    path = Path(name)
    require(not path.is_absolute() and '..' not in path.parts and str(path) == name,
            'invalid archive path')
    return path


def omissions(record, build):
    result = {'ordinary': record['ordinary_sha256'],
              'build/metitarski-counts': record['diagnostic_sha256'],
              'build/observer.o': build['observer_object_sha256']}
    for obj in build['objects']:
        result['build/' + Path(obj['observer_c']).with_suffix('.o').name] = obj['observer_object_sha256']
    return result


def summarize(files, omitted, recipes):
    """Check raw bindings independently of the archive's outer checksum index."""
    record, build = document(files['manifest.json']), document(files['build/build.json'])
    validate_recipes(record, build, recipes)
    require(record['schema'] == 1 and record['status'] == 'completed' and
            record['degrees'] == DEGREES and record['paper_degree'] == 3 and
            record['derived_degrees'] == [5, 7, 9] and record['warmup'] is False and
            record['timing_inference'] is False and record['retries'] == 0 and
            record['affinity'] == [record['cpu']] and record['oracle_version'] == '0.9.0 3.6.0',
            'changed capture protocol')
    require(build['status'] == 'completed' and build['source_head'] == record['commit'] and
            record['kinds'] == build['kinds'] == list(KINDS) and
            record['instrumented_kinds'] == build['instrumented_kinds'] == sorted(KINDS),
            'changed build/source/category binding')
    require(omitted == omissions(record, build), 'unexpected omitted snapshot')
    artifacts = record['artifacts']
    require(set(files) == (set(artifacts) - set(omitted)) | {'manifest.json'},
            'changed retained artifact inventory')
    for name, checksum in artifacts.items():
        relative(name)
        require((omitted[name] if name in omitted else sha(files[name])) == checksum,
                'changed captured artifact: ' + name)
    require(set(record['source_hashes']) == set(SOURCES), 'changed source inventory')
    require(sha(Path(__file__).with_name('meti_counts.py').read_bytes()) ==
            record['source_hashes']['scripts/bench/meti_counts.py'],
            'counter selector changed: use a new archive schema')
    for name, checksum in record['source_hashes'].items():
        require(artifacts['sources/' + name] == checksum, 'changed frozen source binding')
    source_build = [('builder_sha256', 'scripts/bench/build_meti_counts.py'),
                    ('selector_sha256', 'scripts/bench/meti_counts.py'),
                    ('recipe_reader_sha256', 'scripts/bench/build_nested_normalization_counts.py'),
                    ('observer_sha256', 'scripts/bench/ffi/meti_counts.c')]
    for key, name in source_build:
        require(build[key] == record['source_hashes'][name], 'changed builder source binding')
    for key in ['ordinary', 'diagnostic']:
        require(build[key + '_binary_sha256'] == record[key + '_sha256'],
                'changed executable identity')
    require(sha(files['build/labels.h']) == build['labels_sha256'], 'changed counter labels')
    require(files['build/labels.h'].decode() ==
            '#define HEX_METI_KINDS ' + ','.join(map(json.dumps, KINDS)) + '\n',
            'changed counter label order')
    available = set()
    replacements = {}
    require(len(build['commands']) == len(build['objects']) + 3, 'changed build command inventory')
    for i, obj in enumerate(build['objects']):
        copied = files['build/' + Path(obj['observer_c']).name]
        require(sha(copied) == obj['observer_c_sha256'], 'changed generated C')
        prefix = 'extern void hex_meti_count(unsigned);\n'
        text = copied.decode()
        require(text.startswith(prefix), 'missing observer declaration')
        original = re.sub(r'\nhex_meti_count\(\d+\);', '', text[len(prefix):])
        require(sha(original.encode()) == obj['input_sha256'], 'changed original C identity')
        rebuilt, functions = instrument(original)
        require(rebuilt == text and functions == obj['functions'], 'changed C instrumentation')
        require(obj['input'] + '.o.export' in build['link_inputs'], 'unbound original object')
        command = build['commands'][i + 1]
        target = str(Path(obj['observer_c']).with_suffix('.o'))
        require(command[command.index('-o') + 1] == target and
                [arg for arg in command if arg.endswith('.c')] == [obj['observer_c']],
                'changed instrumented compilation recipe')
        replacements[obj['input'] + '.o.export'] = target
        available.update(f['kind'] for f in functions)
    require(sorted(available) == build['instrumented_kinds'], 'changed worker coverage')
    link = build['commands'][-1]
    actual_inputs = [arg for arg in link[3:] if arg.endswith(('.o.export', '.o', '.a'))]
    observer_object = str(Path(link[2]).parent / 'observer.o')
    expected_inputs = [replacements.get(path, path) for path in build['link_inputs']] + [observer_object]
    require(sorted(actual_inputs) == sorted(expected_inputs), 'changed diagnostic link inputs')
    require({arg for arg in link if arg.startswith('-Wl,--wrap=')} ==
            {'-Wl,--wrap=' + symbol for symbol in
             ['lean_nat_gcd', '__gmpz_gcd', '__gmpz_gcdext', 'lean_io_prim_handle_put_str']},
            'changed observer link wrappers')
    commands = record['commands']
    require(len(commands) == 20 and len(record['rows']) == 4, 'incomplete capture schedule')
    for i, command in enumerate(commands):
        require(command['stdout'] == f'{i}.stdout' and command['stderr'] == f'{i}.stderr' and
                command['exit_code'] == 0 and not command.get('incomplete', False) and
                type(command['elapsed_ns']) is int and command['elapsed_ns'] > 0 and
                command['timeout_seconds'] == (1800 if i == 4 else 600),
                'incomplete or changed command')
    require(files['0.stdout'].decode().strip() == record['commit'] ==
            files['18.stdout'].decode().strip() and not files['1.stdout'].strip() and
            not files['19.stdout'].strip(), 'changed source during capture')
    require(files['2.stdout'].decode().strip() == record['lean_version'] and
            'version 4.35.0-rc3,' in record['lean_version'] and
            files['5.stdout'].decode().strip() == record['oracle_version'],
            'changed toolchain/oracle version')
    capture = Path(commands[4]['argv'][2]).parent
    require(Path(commands[4]['argv'][2]).is_absolute() and
            commands[4]['argv'][1] == 'scripts/bench/build_meti_counts.py', 'changed build invocation')
    setup = {0: ['git', 'rev-parse', 'HEAD'], 1: ['git', 'status', '--porcelain'],
             2: ['lake', 'env', 'lean', '--version'], 3: ['lscpu', '--json'],
             18: ['git', 'rev-parse', 'HEAD'], 19: ['git', 'status', '--porcelain']}
    require(all(commands[i]['argv'] == argv for i, argv in setup.items()), 'changed setup command')
    require(commands[5]['argv'][1:] ==
            ['-c', 'import flint; print(flint.__version__,flint.__FLINT_VERSION__)'],
            'changed oracle version invocation')
    fixture = {document(line)['degree']: line + '\n' for line in
               files['sources/conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl'].decode().splitlines()}
    require(sorted(fixture) == DEGREES, 'changed functional fixture inventory')
    rows = []
    for i, degree in enumerate(DEGREES):
        row = record['rows'][i]
        control, observed, oracle = commands[6 + 3*i:9 + 3*i]
        require(row['degree'] == degree and row['ordinary'] == control['stdout'] and
                row['fixture'] == observed['stdout'] and row['counters'] == observed['stderr'] and
                row['oracle'] == oracle['stdout'], 'changed row/command binding')
        require(control['argv'][0] == str(capture / 'ordinary') and
                observed['argv'][0] == str(capture / 'build/metitarski-counts') and
                control['argv'][1:] == observed['argv'][1:] == ['metitarski', 'counts', str(degree)] and
                oracle['argv'][1] == 'scripts/oracle/real_closure_metitarski_scaling.py' and
                oracle['argv'][0] == commands[5]['argv'][0] and
                oracle['argv'][2] == str(capture / row['fixture']), 'changed executed input')
        check_packet(files[row['ordinary']].decode(), fixture[degree], degree)
        packet = check_packet(files[row['fixture']].decode(), fixture[degree], degree)
        events = [s for s in files[control['stderr']].decode().splitlines() if s.startswith('METI ')]
        require(events == ['METI BEGIN', 'METI END'], 'changed ordinary region')
        counts = parse_record(files[row['counters']].decode())
        require(counts == row['observed'], 'changed counter/summary binding')
        expected = dict(oracle='FLINT qqbar', degree=degree, real_roots=1, multiplicity=1,
                        head_bytes=len(json.dumps(packet['head'], separators=(',', ':')).encode()),
                        descriptor_bytes=len(json.dumps(packet['root'], separators=(',', ':')).encode()))
        require(document(files[row['oracle']]) == expected, 'changed oracle/packet binding')
        rows.append(dict(degree=degree, **counts['counts'],
                         **{k: counts[k] for k in ['lean_nat_gcd', 'gmp_gcd', 'gmp_gcdext']}))
    return dict(schema=1, source=record['commit'], cpu=record['cpu'],
                commands=len(commands), instrumented_modules=len(build['objects']),
                linked_inputs=len(build['link_inputs']), timing_inference=False, rows=rows)


def table(result):
    keys = ['degree', 'poly_gcd', 'poly_xgcd_left', 'gcd_loop_tests', 'yun_loop_tests',
            'signed_chains', 'chain_loop_tests', 'bkr_solves', 'bisection_nodes',
            'algebraic_sign_reads', 'algebraic_sign_poly', 'lean_nat_gcd', 'gmp_gcd']
    require(all(row[key] == 0 for row in result['rows'] for key in set(row) - set(keys)),
            'unreported nonzero counter')
    lines = [BEGIN, f"Source: `{result['source']}`; CPU {result['cpu']}; "
             f"{result['commands']} commands; {result['instrumented_modules']} instrumented modules; "
             f"{result['linked_inputs']} original link inputs.", '',
             '| ' + ' | '.join(keys) + ' |', '| ' + ' | '.join(['---']*len(keys)) + ' |']
    lines += ['| ' + ' | '.join(str(row[k]) for k in keys) + ' |' for row in result['rows']]
    lines += ['', 'All other instrumented categories and `gmp_gcdext` are zero at every rung.', END]
    return '\n'.join(lines)


def unpack(path):
    files = {}
    with tarfile.open(path, 'r:gz') as archive:
        total = 0
        for entry in archive:
            relative(entry.name)
            total += entry.size
            require(entry.isfile() and entry.name not in files and total <= 64*1024*1024,
                    'invalid, duplicate or oversized archive member')
            files[entry.name] = archive.extractfile(entry).read()
    return files


def verify(folder):
    require(not folder.is_symlink() and not any(p.is_symlink() for p in folder.iterdir()),
            'redirected archive')
    index = document((folder / 'archive.json').read_bytes())
    require(index['schema'] == 'metitarski-counts-v1', 'wrong archive schema')
    require({p.name for p in folder.iterdir()} ==
            {'capture.tar.gz', 'archive.json', 'analysis.json', 'README.md', 'recipes.json'},
            'changed archive inventory')
    require(sha((folder / 'capture.tar.gz').read_bytes()) == index['archive_sha256'],
            'changed compressed archive')
    files = unpack(folder / 'capture.tar.gz')
    require({name: sha(data) for name, data in files.items()} == index['files'],
            'changed archive member index')
    recipe_data = (folder / 'recipes.json').read_bytes()
    require(sha(recipe_data) == index['recipes_sha256'], 'changed recipe supplement')
    result = summarize(files, index['omitted_snapshots'], document(recipe_data))
    require(index['source'] == result['source'], 'changed archive source')
    require(document((folder / 'analysis.json').read_bytes()) == result, 'changed derived analysis')
    report = (folder / 'README.md').read_text()
    require(report.count(BEGIN) == report.count(END) == 1 and table(result) in report,
            'changed reported counts')
    return result


def create(capture, folder):
    record = document((capture / 'manifest.json').read_bytes())
    build = document((capture / 'build/build.json').read_bytes())
    omitted = omissions(record, build)
    require({str(p.relative_to(capture)) for p in capture.rglob('*') if p.is_file()} ==
            set(record['artifacts']) | {'manifest.json'}, 'changed raw capture inventory')
    for name, checksum in record['artifacts'].items():
        path = capture / relative(name)
        require(not path.is_symlink(), 'redirected capture artifact')
        with path.open('rb') as stream:
            require(hashlib.file_digest(stream, 'sha256').hexdigest() == checksum,
                    'changed raw artifact: ' + name)
    files = {name: (capture / name).read_bytes() for name in
             (set(record['artifacts']) - set(omitted)) | {'manifest.json'}}
    from scripts.bench.meti_recipes import collect
    recipes = collect(capture, Path(__file__).resolve().parents[2])
    result = summarize(files, omitted, recipes)
    # The report is authored first; never overwrite a pre-existing capture.
    require({p.name for p in folder.iterdir()} == {'README.md'}, 'archive destination is not new')
    with (folder / 'capture.tar.gz').open('wb') as out, gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w', format=tarfile.USTAR_FORMAT) as archive:
            for name, data in sorted(files.items()):
                entry = tarfile.TarInfo(name)
                entry.size, entry.mode = len(data), 0o644
                archive.addfile(entry, io.BytesIO(data))
    index = dict(schema='metitarski-counts-v1', source=record['commit'],
                 archive_sha256=sha((folder / 'capture.tar.gz').read_bytes()),
                 omitted_snapshots=omitted, files={name: sha(data) for name, data in sorted(files.items())})
    recipe_data = (json.dumps(recipes, indent=2, sort_keys=True) + '\n').encode()
    (folder / 'recipes.json').write_bytes(recipe_data)
    index['recipes_sha256'] = sha(recipe_data)
    for name, data in [('archive.json', index), ('analysis.json', result)]:
        (folder / name).write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')
    report = folder / 'README.md'
    require(BEGIN not in report.read_text(), 'report already contains counts')
    report.write_text(report.read_text() + '\n' + table(result) + '\n')
    return verify(folder)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--capture', type=Path)
    parser.add_argument('--archive', type=Path, default=ARCHIVE)
    args = parser.parse_args()
    result = create(args.capture, args.archive) if args.capture else verify(args.archive)
    print(json.dumps(result, indent=2))
