#!/usr/bin/env python3
"""Check retained source-packet observations, not mathematical soundness."""
from pathlib import Path
import argparse, gzip, hashlib, io, json, statistics, subprocess, tarfile

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = next(p for p in here.parents if (p / '.git').exists())
sha = lambda raw: hashlib.sha256(raw).hexdigest()
manifest = json.loads((here / 'manifest.json').read_text())
for name, digest in manifest['artifacts'].items():
    assert sha((here / name).read_bytes()) == digest, name
resources = json.loads((here / 'resource-audit.json').read_text())
assert resources['systemd']['MemoryMax'] == '34359738368'
assert resources['systemd']['MemorySwapMax'] == '0'
assert resources['workers'] and all(w['cpu_affinity'] == '38' and w['LEAN_NUM_THREADS'] == '2' for w in resources['workers'])
context = json.loads((here / 'context.json').read_text())
assert context['status'] == 'complete' and not context['dirty']
assert context['blocks'] == 5 and len(context['cases']) == 22
assert context['arms'] == ['lexical', 'parsed', 'restored', 'replayed']
assert len(context['compiler_imports']) == 449
assert not any(m == 'Mathlib' or m.startswith('Mathlib.') for m in context['compiler_imports'])
for name, digest in context['source_sha256'].items():
    original = subprocess.check_output(['git', 'show', context['revision'] + ':' + name], cwd=root)
    assert sha(original) == digest, name
    if args.check_head:
        assert sha((root / name).read_bytes()) == digest, name
for key, name in [('driver_sha256', 'driver.lean.txt'),
                  ('benchmark_sha256', 'benchmark.lean.txt'),
                  ('generator_sha256', 'generator.lean.txt'),
                  ('collector_sha256', 'collector.py.txt')]:
    assert sha((here / name).read_bytes()) == context[key], name
bench = (here / 'benchmark.lean.txt').read_text()
assert 'repeats := 1, warmupFirstIter := true, minTotalSeconds := 0.2' in bench
assert 'maxSecondsPerCall := 30.0, expectedHash := some (Hashable.hash true)' in bench
assert 'IO.Ref ByteArray' in bench and 'input.get' in bench
assert '#eval' not in (here / 'driver.lean.txt').read_text()
expected = [(b, case[0], arm) for b in range(5) for case in context['cases']
            for arm in (context['arms'] if b % 2 == 0 else list(reversed(context['arms'])))]
assert len(expected) == 440
assert [(s['block'], s['case'], s['arm']) for s in context['samples']] == expected
summaries = {(r['case'], r['arm']): r for r in json.loads((here / 'summary.json').read_text())}
assert len(summaries) == 88
values = {}
with tarfile.open(here / 'samples.tar.gz', 'r:gz') as archive:
    def raw(name):
        return archive.extractfile(name).read()
    assert json.loads(raw('context.json')) == context
    for sample in context['samples']:
        assert sample['exit_code'] == 0 and sample['elapsed_seconds'] > 0
        exported = json.loads(raw(sample['stem'] + '.json'))
        assert len(exported['results']) == 1
        result = exported['results'][0]
        assert result['function'] == 'SourceReplayBench.' + sample['arm']
        config = result['config']
        assert config['repeats'] == 1 and config['warmup_first_iter'] and config['warmup']
        assert config['min_total_seconds'] == 0.2 and config['max_seconds_per_call'] == 30
        assert config['expected_hash'] == result['observed_hash']
        assert result['expected_hash_check']['status'] == 'match' and result['hashes_agree']
        assert len(result['points']) == 1 and not result['budget_truncated']
        point = result['points'][0]
        assert point['status'] == 'ok' and point['inner_repeats'] > 0
        assert point['total_nanos'] > 0 and point['peak_rss_kb'] > 0
        assert sample['max_rss_kib'] > 0
        values.setdefault((sample['case'], sample['arm']), []).append(
            point['total_nanos'] / point['inner_repeats'] / 1000)
        raw(sample['stem'] + '.stdout.txt')
        raw(sample['stem'] + '.stderr.txt')
for key, observations in values.items():
    assert len(observations) == 5
    row = summaries[key]
    for field, value in [('median_microseconds', statistics.median(observations)),
                         ('min_microseconds', min(observations)),
                         ('max_microseconds', max(observations))]:
        assert row[field] == value, (key, field)
with tarfile.open(here / 'inputs.tar.gz', 'r:gz') as archive:
    assert json.loads(archive.extractfile('manifest.json').read()) == context['cases']
    for case in context['cases']:
        name, axis, parameter, degree, atoms, bits, precision, depth, nbytes, unique, expanded = case
        packet = archive.extractfile(name + '.json').read()
        assert sha(packet) == context['input_sha256'][name] and len(packet) == nbytes
        data = json.loads(packet)
        assert len(data) == 4 and len(data[1]) == atoms and len(data[2]) == atoms
        version, selected, entries = data[3]
        assert version == 1 and len(entries) == unique and 0 <= selected < unique
        sizes = []
        for index, (_, children) in enumerate(entries):
            assert len(children) in (0, 1)
            if not children:
                sizes.append(1)
            else:
                left, right = children[0]
                assert 0 <= left < index and 0 <= right < index
                sizes.append(1 + sizes[left] + sizes[right])
        assert sizes[selected] == expanded, name
        baseline = [2, 2, 16, 0, 0]
        actual = [degree, atoms, bits, precision, depth]
        if axis in ['degree', 'atoms', 'bits', 'precision', 'depth']:
            baseline[['degree', 'atoms', 'bits', 'precision', 'depth'].index(axis)] = parameter
            assert actual == baseline, name
with tarfile.open(here / 'preparation.tar.gz', 'r:gz') as archive:
    controls = archive.extractfile('source-replay-controls-4.log').read().decode()
    assert 'code=exited, status=0/SUCCESS' in controls
    assert '9 malformed/false evidence controls passed' in controls
    assert 'byte/depth/digit limits' in controls
    for name in ['source-replay-bench-build-1.log', 'source-replay-matrix-3.log']:
        assert 'code=exited, status=0/SUCCESS' in archive.extractfile(name).read().decode(), name
log = gzip.decompress((here / 'collection.log.gz').read_bytes()).decode()
assert 'retained 440 completed samples' in log
assert 'code=exited, status=0/SUCCESS' in log
print('Verified 440 retained observations/22 inputs/four cumulative stages; source bindings, hashes, schedule, DAG sizes and scoped controls. Full #10358 remains incomplete.')
