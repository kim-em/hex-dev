#!/usr/bin/env python3
"""Verify quotient-reader and Boolean-branch quotation evidence."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[2]
record = json.loads((root / 'context.json').read_text())
git = lambda *arguments: subprocess.check_output(['git', *arguments], cwd=repo)
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def artifact(path):
    return gzip.decompress((root / path).read_bytes()).decode()

def log(key):
    return artifact(record['validation'][key])

assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == digest, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == digest, path
if args.check_head:
    paths = git('diff', '--name-only', record['source_commit']).decode().splitlines()
    paths += git('ls-files', '--others', '--exclude-standard').decode().splitlines()
    assert all(path.startswith('reports/') for path in paths), paths
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git(
        'show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in record['validation']:
    assert 'code=exited, status=0/SUCCESS' in log(key), key
assert 'Build completed successfully (14383 jobs)' in log('integration')
manual = artifact('diagnostics/branch-seal-integration-3.log.gz')
assert 'Built HexManual (' in manual
assert 'sign packet audit inventory changed: 100 theorem bodies/11 definitions; traces=101' in manual
for message in [
    'quotient-backed formula reader: exact/below budget=92; rejection and caller rollback checked',
    'quotient quotation actual bodies: 9 theorems/4 definitions; nonempty traces=4',
    'generic rational quotation: 205 actual theorem bodies',
    'dependent quotation actual bodies: 153 theorems/16 definitions; nonempty traces=78',
    'retained root/context actual bodies: 821 theorems/63 definitions; nonempty traces=869',
    'public packet actual bodies: 706 theorems/67 definitions; nonempty traces=763',
    'root/header packet actual bodies: 724 theorems/66 definitions; nonempty traces=775',
    'root context actual bodies: 732 theorems/68 definitions; nonempty traces=785',
    'root-table quotation: 97 theorem bodies, 14 data definitions',
    'sign packet quotation: 100 theorem bodies, 11 definitions',
    'sign packet nonempty diagnostic traces: 101',
    'sign packet final exhaustion: 71309+23']:
    assert message in log('integration'), message
core = git('show', record['source_commit'] + ':adapters/HexRCF/RealCoefficients/RootQuote.lean')
assert artifact('diagnostics/frozen-14-RootQuote.lean.txt.gz').encode() == core
assert 'application type mismatch' in artifact('diagnostics/fresh-complete-frozen-13.log.gz')
failure = artifact('diagnostics/fresh-complete-frozen-14.log.gz')
assert 'limit 2000000, consumed 1998337, requested 1664' in failure
assert 'status=1/FAILURE' in failure and '14min 42.791s' in failure
assert 'boundary 800:' in artifact('diagnostics/fresh-complete-frozen-14-progress.log.gz')
assert record['complete_packet_accepted'] is False
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = artifact('validation/memory-policy.txt.gz')
assert all(value in memory for value in ['ActiveState=active', 'MemoryMax=34359738368',
                                       'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
assert {(item['label'], item['kind']) for item in inspection} == {
    (label, kind) for label in ['desktop', 'narrow'] for kind in ['introduction', 'example', 'budget']}
assert all(item['descendantOverflow'] <= 1 and item['targetScrollWidth'] <= item['targetWidth'] + 1
           for item in inspection)
assert len(record['visually_inspected_captures']) == 6
assert 'Saved quotient quotation desktop/narrow screenshots' in log('browser')
assert len(record['compiled_files']) == 4 and all(item['bytes'] > 0 for item in record['compiled_files'])
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '9/4/4 quotient bodies, strict compatibility inventories, manual and six captures; '
      'complete-cell acceptance remains unproved')
