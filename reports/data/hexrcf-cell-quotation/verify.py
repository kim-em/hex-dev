#!/usr/bin/env python3
"""Verify the fixed-input cell quotation evidence and its source binding."""
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
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: gzip.decompress((root / p).read_bytes()).decode()
log = lambda key: read(record['validation'][key])

assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == digest, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == digest, path
if args.check_head:
    paths = git('diff', '--name-only', record['source_commit']).decode().splitlines()
    paths += git('ls-files', '--others', '--exclude-standard').decode().splitlines()
    assert all(p.startswith('reports/') for p in paths), paths
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git('show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in record['validation']:
    assert 'code=exited, status=0/SUCCESS' in log(key), key
assert 'Build completed successfully (14427 jobs)' in log('integration')
for text in [
    'staged zero true: nodes=502481', 'staged zero false: nodes=502483',
    'staged two-root quadratic true: nodes=14294138',
    'finite family checked: 2 entries; nodes=4441813',
    'finite family checked: 3 entries; nodes=14292933',
    'staged exact/below/wrong-goal and full caller restoration checked',
    'staged replay proves its original constant source; false verdict cannot prove that source',
    'staged malformed cells, original zero guard, terminal callback and full rollback checked']:
    assert text in log('controls'), text
assert '1409 theorems/78 definitions; nonempty traces=1439' in log('audit')
for text in ['retained packet exact/one-below request budget=3382239',
             'retained packet wrong-sign rejection restored caller declarations and metavariables',
             'malformed retained input refused with caller rollback: variant=2',
             'source selection: 14 exported theorem bodies checked in a fresh module']:
    assert text in log('integration'), text
assert 'recursive scalar quotation: 87 theorem bodies, 5 definitions' in log('recursive')
assert 'recursive variants: constant=28294; tagged=28307; retry=31022' in log('recursive')
assert 'recursive exhausted: consumed=29391, requested=925' in log('recursive')
assert 'maximum number of heartbeats (12000000)' in read('diagnostics/cell-pointwise-quadratic-5.log.gz')
assert 'limit 12000000, consumed 12000000, requested 1' in read('diagnostics/cell-pointwise-stage-profile-2.log.gz')
assert 'status=1/FAILURE' in read('diagnostics/fresh-staged-2.log.gz')
assert record['constant_source_accepted'] and record['rational_quadratic_packet_accepted']
assert record['algebraic_original_source_accepted'] is False
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {x['name'] for x in metadata} == {'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(x['exit_code'] == 0 for x in metadata)
memory = read('validation/cell-quotation-memory-policy.txt.gz')
assert all(x in memory for x in ['ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
kinds = ['types', 'callbacks', 'packet', 'stages', 'packetcode', 'trace', 'example', 'measurements', 'audit']
assert {(x['label'], x['kind']) for x in inspection} == {(a, b) for a in ['desktop', 'narrow'] for b in kinds}
assert all(x['descendantOverflow'] == 0 and x['targetScrollWidth'] <= x['targetWidth'] + 1 for x in inspection)
review = json.loads((root / 'captures/visual-review.json').read_text())
assert len(review['captures']) == 18
for item in review['captures']:
    assert item['viewed'] and sha((root / item['path']).read_bytes()) == item['sha256']
assert len(record['compiled_files']) == 4 and all(x['bytes'] > 0 for x in record['compiled_files'])
print(f'Verified {len(record["artifacts"])} artifacts/{len(record["sources"])} sources; '
      '37 targets/manual, fixed quadratic packet, constant source and 18 inspected captures; '
      'general algebraic source assembly remains incomplete')
