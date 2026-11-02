#!/usr/bin/env python3
"""Verify replay helper type quotation evidence."""
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
assert 'Build completed successfully (14398 jobs)' in log('integration')
for message in [
 'typed replay helper actual bodies: 96 theorems/3 definitions; nonempty traces=99',
 'typed replay helper array/7: proofNodes=95378',
 'typed replay helper array/8: proofNodes=8388',
 'typed replay helper helper/7: proofNodes=81812',
 'typed replay helper helper/8: proofNodes=7272',
 'typed helper exact/below/wrong-goal and caller rollback: array; exact=95378',
 'typed helper exact/below/wrong-goal and caller rollback: helper; exact=81812',
 'retained packet exact/one-below request budget=3029330; caller state restored',
 'retained packet wrong-sign rejection restored caller declarations and metavariables',
 'malformed retained input refused with caller rollback: variant=2',
 'selected projection quotation actual bodies: 70 theorems/8 definitions; nonempty traces=72',
 'dependent replay boundary actual bodies: 132 theorems/3 definitions; nonempty traces=135']:
    assert message in log('integration'), message
assert 'recursive scalar quotation: 87 theorem bodies, 5 definitions' in log('recursive')
assert 'recursive variants: constant=23526; tagged=23537; retry=26175' in log('recursive')
assert 'recursive exhausted: consumed=24544, requested=925' in log('recursive')
assert 'Built HexRCF.RootQuoteCases' in log('prefix')
failure=artifact('diagnostics/fresh-complete-projected-2.log.gz')
assert '45min 55.490s' in failure and 'status=1/FAILURE' in failure
assert 'evidence.table hc' in failure and 'application type mismatch' in failure
assert record['complete_packet_accepted'] is False
assert 'consumed 2998466, requested 1535' in artifact('diagnostics/replay-helper-integration-2.log.gz')
assert 'maximum number of heartbeats (12000000)' in artifact('diagnostics/replay-helper-focused-1.log.gz')
metadata=json.loads((root/'validation/metadata.json').read_text())
assert {x['name'] for x in metadata}=={'copyright','lines','dag','admissions','selected-admissions','relative','diff'}
assert all(x['exit_code']==0 for x in metadata)
memory=artifact('validation/replay-helper-memory-policy.txt.gz')
assert all(x in memory for x in ['ActiveState=active','MemoryMax=34359738368','MemorySwapMax=0','OOMPolicy=kill','LEAN_NUM_THREADS=2'])
inspection=json.loads((root/'captures/inspection.json').read_text())
assert {(x['label'],x['kind']) for x in inspection}=={(a,b) for a in ['desktop','narrow'] for b in ['types','controls','budgets','recursive','packet']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in inspection)
review=json.loads((root/'captures/visual-review.json').read_text())
assert len(review['captures'])==10
for item in review['captures']:
    assert item['viewed'] is True and item['local_overflow']==0
    assert sha((root/item['path']).read_bytes())==item['sha256']
assert len(record['compiled_files'])==4 and all(x['bytes']>0 for x in record['compiled_files'])
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '96/3/99 helper audit, all33 selected targets, complete manual and ten inspected captures; '
      'complete original-source acceptance remains unproved by this record')
