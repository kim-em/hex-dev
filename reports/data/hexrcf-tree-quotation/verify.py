#!/usr/bin/env python3
"""Verify public replay-tree quotation evidence."""
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
assert 'Build completed successfully (14388 jobs)' in log('integration')
assert 'Built HexManual (' in log('render')
for message in [
    'public replay quotation actual bodies: 254 theorems/4 definitions; nonempty traces=246',
    'generic rational quotation: 208 actual theorem bodies',
    'actual cubic and conditional quotation bodies under kernel producer diagnostics: 265',
    'dependent quotation actual bodies: 153 theorems/16 definitions; nonempty traces=78',
    'retained root/context actual bodies: 827 theorems/63 definitions; nonempty traces=875',
    'public packet actual bodies: 712 theorems/67 definitions; nonempty traces=769',
    'root/header packet actual bodies: 730 theorems/66 definitions; nonempty traces=781',
    'root context actual bodies: 738 theorems/68 definitions; nonempty traces=791',
    'root-table quotation: 103 theorem bodies, 14 data definitions',
    'sign packet quotation: 109 theorem bodies, 11 definitions',
    'sign packet nonempty diagnostic traces: 110',
    'sign packet final exhaustion: 79508+23',
    'retained packet exact/one-below request budget=2405322',
    'wrong-context/swapped-child reader failures and caller rollback checked']:
    assert message in log('integration'), message
failure=artifact('diagnostics/fresh-complete-replay-1.log.gz')
assert 'limit 5000000, consumed 5000000, requested 1' in failure
assert 'status=1/FAILURE' in failure and '38min 13.237s' in failure
progress=artifact('diagnostics/fresh-complete-replay-1-progress.log.gz')
assert 'boundary 2000:' in progress and 'original source reified' in progress
assert 'complete literal acceptance checked' not in progress
assert record['complete_packet_accepted'] is False
core=git('show',record['source_commit']+':adapters/HexRCF/RealCoefficients/RootQuote.lean')
assert artifact('diagnostics/replay-boundary-RootReplayQuoteProbe.lean.txt.gz').encode()==core.replace(b'RootQuote',b'RootReplayQuoteProbe')
assert 'exact saved target accepted with public Replay.check.eq_1' in artifact('diagnostics/quote-snapshot-explicit-3.log.gz')
assert 'status=0/SUCCESS' in artifact('diagnostics/quote-snapshot-explicit-3.log.gz')
assert 'snapshot wrong-goal data rejected by the ordinary kernel' in artifact('diagnostics/quote-snapshot-read-3.log.gz')
assert record['snapshot']['last_check']=='start RootSnapshotProbe.step'
assert record['snapshot']['snapshot_bytes']>0 and len(record['snapshot']['snapshot_sha256'])==64
metadata=json.loads((root/'validation/metadata.json').read_text())
assert {x['name'] for x in metadata}=={'copyright','lines','dag','admissions','selected-admissions','relative','diff'}
assert all(x['exit_code']==0 for x in metadata)
assert '15 changed/new Lean files' in artifact('validation/tree-quote-metadata-selected-admissions.log.gz')
memory=artifact('validation/tree-memory-policy.txt.gz')
assert all(x in memory for x in ['ActiveState=active','MemoryMax=34359738368','MemorySwapMax=0','OOMPolicy=kill','LEAN_NUM_THREADS=2'])
inspection=json.loads((root/'captures/inspection.json').read_text())
assert {(x['label'],x['kind']) for x in inspection}=={(a,b) for a in ['desktop','narrow'] for b in ['introduction','example','budget']}
assert all(x['descendantOverflow']==0 and x['targetScrollWidth']<=x['targetWidth']+1 for x in inspection)
review=json.loads((root/'captures/visual-review.json').read_text())
assert len(review['captures'])==len(record['visually_inspected_captures'])==6
for item in review['captures']:
    assert item['viewed'] is True and item['local_overflow']==0
    assert sha((root/'captures'/item['path']).read_bytes())==item['sha256']
assert 'Changed content overflows' in artifact('diagnostics/narrow-overflow/tree-quotation-browser-1.log.gz')
assert len(record['compiled_files'])==4 and all(x['bytes']>0 for x in record['compiled_files'])
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '254/4/246 public-tree audit, strict compatibility, complete manual and six inspected captures; '
      'complete-packet acceptance remains unproved')
