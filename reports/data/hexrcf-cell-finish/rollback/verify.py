#!/usr/bin/env python3
"""Verify the test-only joint rollback supplement without repinning its parent."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[3]
sha = lambda raw: hashlib.sha256(raw).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
record = json.loads((root / 'context.json').read_text())
subprocess.run([sys.executable, str(root.parent / 'verify.py')], check=True)
assert sha((root.parent / 'context.json').read_bytes()) == record['parent_context_sha256']
changed = git('diff', '--name-only', record['parent_source_commit'],
              record['source_commit']).decode().splitlines()
assert [p for p in changed if not p.startswith('reports/')] == ['conformance/HexRCF/CellFinishCases.lean']
for name, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + name)) == digest, name
    if args.check_head:
        assert sha((repo / name).read_bytes()) == digest, name
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
assert all(x['exit_code'] == 0 for x in record['checks'])
log = gzip.decompress((root / 'build.log.gz').read_bytes()).decode()
for text in ['code=exited, status=0/SUCCESS',
             'joint late finishing exhaustion restored quotation declarations: limit=448468; consumed=448274; requested=195',
             'joint replay and original-source finishing proofNodes=448469',
             '163 theorems/43 definitions; nonempty traces=170']:
    assert text in log, text
assert '2394 local modules, no admissions' in (root / 'metadata.log').read_text()
patch = (root / 'source.patch').read_text()
assert 'declarations.get) > names.size' in patch and 'restored before sentinel (some names)' in patch
print('Verified test-only late finishing exhaustion, quotation-declaration/MCtx rollback and fresh audit; 108 source bindings')
