#!/usr/bin/env python3
"""Verify stored-row and dependent replay quotation evidence."""
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
assert 'Build completed successfully (14396 jobs)' in log('integration')
assert 'Built HexManual (' in log('render')
controls = log('controls')
for message in [
    'selected projection quotation actual bodies: 70 theorems/8 definitions; nonempty traces=72',
    'dependent replay boundary actual bodies: 132 theorems/3 definitions; nonempty traces=135',
    'projection exact/below budget and caller rollback checked; exact=2479',
    'projection depth=1; proofNodes=2001; below refused',
    'projection depth=16; proofNodes=4962; below refused',
    'projection depth=24; proofNodes=6758; below refused',
    'dependent replay helper inline/7: proofNodes=58360',
    'dependent replay helper inline/8: proofNodes=5376',
    'dependent replay helper stored/7: proofNodes=57166',
    'dependent replay helper stored/8: proofNodes=5108',
    'boundary exact/below/wrong-goal and caller rollback checked; exact=57166']:
    assert message in controls, message
assert 'recursive variants: constant=15002; tagged=15013; retry=17268' in log('recursive')
assert 'recursive exhausted: consumed=15637, requested=925' in log('recursive')
assert 'protected codec, wrong second sign, trailing zero and malformed heads checked with rollback' in log('hidden')
failure = artifact('diagnostics/fresh-complete-projected-1.log.gz')
assert 'status=1/FAILURE' in failure and '46min 13.203s' in failure
assert 'replayBoundary' in failure and 'application type mismatch' in failure.lower()
assert record['complete_packet_accepted'] is False
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {x['name'] for x in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(x['exit_code'] == 0 for x in metadata)
memory = artifact('validation/row-memory-policy.txt.gz')
assert all(x in memory for x in [
    'ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0',
    'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
assert {(x['label'], x['kind']) for x in inspection} == {
    (a, b) for a in ['desktop', 'narrow'] for b in ['introduction', 'api', 'example', 'budget']}
assert all(x['descendantOverflow'] == 0 and
           x['targetScrollWidth'] <= x['targetWidth'] + 1 for x in inspection)
review = json.loads((root / 'captures/visual-review.json').read_text())
assert review['viewed_all_eight'] is True and len(review['captures']) == 8
for item in review['captures']:
    assert item['viewed'] is True
    assert sha((root / item['path']).read_bytes()) == item['sha256']
assert 'Changed content overflows' in artifact('diagnostics/row-quotation-browser-1.log.gz')
assert len(record['compiled_files']) == 5 and all(x['bytes'] > 0 for x in record['compiled_files'])
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '70/8/72 row and 132/3/135 boundary audits, 32 targets, manual and eight inspected captures; '
      'complete original-source acceptance remains unproved by this record')
