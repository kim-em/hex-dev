#!/usr/bin/env python3
"""Validate retained nested measurements, frozen sources and published tables."""
import json
from pathlib import Path

from analyze_real_closure_nested import digest, summarize


class Protocol:
    """Historical nested-clean-eager-v1 schedule; independent of live capture code."""
    PARAMETERS = [(depth, steps) for depth in (1, 2) for steps in (2, 4, 8, 16)]
    TRIALS = 6
    TARGET_NANOS = 500_000_000

    @staticmethod
    def benchmark(depth, steps, arm):
        return ('Hex.RealClosure.NestedNormalization.Measure.Depth' + str(depth)
                + '.' + ('clean' if arm == 'A' else 'eager') + str(steps))

    @classmethod
    def schedule(cls):
        return [(trial, depth, steps, arm) for trial in range(cls.TRIALS)
                for depth, steps in cls.PARAMETERS for arm in ('AB' if trial % 2 == 0 else 'BA')]


SOURCES = {'analyzer_sha256': 'sources/analyze_real_closure_nested.py',
           'capture_script_sha256': 'sources/real_closure_nested_measurement.py',
           'protocol_sha256': 'sources/real-closure-nested-protocol.md',
           'oracle_sha256': 'sources/real_closure_nested_normalization.py'}
TIMING_HEADER = '| Depth | Products | Clean median ms (full range) | Eager median ms (full range) | Paired eager/clean median (full range) | Direction |'
GROWTH_HEADER = '| Depth | Products | Stored degrees by level clean/eager | Stored bytes clean/eager | Stored coefficient bits clean/eager | Final query graph bytes clean/eager |'


def checked_path(folder, name):
    path = Path(name)
    if (not name or path.is_absolute() or path.as_posix() != name
            or any(part in ('.', '..') for part in path.parts)):
        raise ValueError('invalid archive path: ' + name)
    result = folder / path
    if result.is_symlink() or not result.is_file() or result.resolve() != folder.resolve() / path:
        raise ValueError('missing or redirected archive file: ' + name)
    return result


def timing_table(result):
    rows = [TIMING_HEADER, '| ---: | ---: | --- | --- | --- | --- |']
    for r in result['summary']:
        def interval(value, bounds):
            return f'{value:.6f} ({bounds[0]:.6f}–{bounds[1]:.6f})'
        rows.append(f'| {r["depth"]} | {r["steps"]} | '
                    + interval(r['clean_ms'], r['clean_range_ms']) + ' | '
                    + interval(r['eager_ms'], r['eager_range_ms']) + ' | '
                    + interval(r['paired_eager_over_clean_median'], r['paired_eager_over_clean_range'])
                    + f' | {r["direction"]} |')
    return '\n'.join(rows)


def growth_table(folder, manifest):
    rows = [GROWTH_HEADER, '| ---: | ---: | --- | ---: | ---: | ---: |']
    for check in manifest['functional_checks']:
        pair = json.loads((folder / check['oracle_output']).read_text())['results']
        degrees = ' / '.join(str(r['stored']['max_degree_by_level']) for r in pair)
        size = ' / '.join(str(r['stored']['serialized_bytes']) for r in pair)
        bits = ' / '.join(str(r['stored']['total_coefficient_bits']) for r in pair)
        evidence = ' / '.join(str(r['query']['graph_serialized_bytes']) for r in pair)
        rows.append(f'| {check["depth"]} | {check["steps"]} | {degrees} | {size} | {bits} | {evidence} |')
    return '\n'.join(rows)


def check_table(readme, table):
    header = table.splitlines()[0]
    if readme.count(header) != 1:
        raise ValueError('missing or repeated published table header')
    lines = readme[readme.index(header):].splitlines()
    actual = []
    for line in lines:
        if not line.startswith('|'):
            break
        actual.append(line)
    if '\n'.join(actual) != table:
        raise ValueError('published table differs from retained observations')


def check_archive(folder):
    archive = json.loads((folder / 'archive.json').read_text())
    manifest = json.loads((folder / 'manifest.json').read_text())
    if archive['schema'] != 'nested-clean-eager-v1' or archive['sources'] != SOURCES:
        raise ValueError('unknown archive schema or frozen source inventory')
    omitted = archive['omitted_snapshot']
    binary = 'hexrealclosure_nested_normalization'
    if (omitted['filename'] != binary or omitted['size'] != 120771072
            or omitted['sha256'] != manifest['executable_sha256']
            or manifest['artifacts'].get(binary) != omitted['sha256']
            or archive['captured_commit'] != manifest['commit']):
        raise ValueError('archive source or omitted snapshot binding failed')
    expected = (set(manifest['artifacts']) - {binary}) | {'manifest.json', 'analysis.json'} | set(SOURCES.values())
    actual = {p.relative_to(folder).as_posix() for p in folder.rglob('*') if p.is_file()}
    if (set(archive['files']) != expected or actual != expected | {'archive.json', 'README.md'}
            or len(manifest['commands']) != 131 or len(expected) != 399):
        raise ValueError('archive file or command inventory differs')
    for name, expected_digest in archive['files'].items():
        if digest(checked_path(folder, name)) != expected_digest:
            raise ValueError('archive digest differs: ' + name)
    identities = {key: checked_path(folder, name) for key, name in SOURCES.items()}
    result = summarize(folder, protocol=Protocol, identities=identities, omitted_snapshot=omitted)
    if result != json.loads((folder / 'analysis.json').read_text()):
        raise ValueError('committed analysis differs from retained observations')
    readme = (folder / 'README.md').read_text()
    check_table(readme, timing_table(result))
    check_table(readme, growth_table(folder, manifest))
    return result
