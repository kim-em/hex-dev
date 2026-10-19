#!/usr/bin/env python3
"""Verify source-selection test allowance and retained failures."""
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

for path,digest in record['sources'].items():
    assert sha(git('show',record['source_commit']+':'+path))==digest,path
    if args.check_head: assert sha((repo/path).read_bytes())==digest,path
for item in record['artifacts']:
    raw=(root/item['path']).read_bytes()
    assert len(raw)==item['bytes'] and sha(raw)==item['sha256'],item['path']
    assert sha(gzip.decompress(raw))==item['uncompressed_sha256'],item['path']
validation=artifact('source-selection-ci-repair-1.log.gz')
for text in ['code=exited, status=0/SUCCESS','source-selection root quotation proofNodes=1347886',
 'source selection: 14 exported theorem bodies checked in a fresh module',
 'source-selection inspection: 374 theorem bodies/97 definitions; 438 nonempty traces']:
    assert text in validation,text
ci=json.loads(artifact('helper-ci39119984084-final.json.gz'))
assert ci['headSha']=='287f54f01aa675c26b10aeefcb427f16a2a61aea' and ci['conclusion']=='failure'
assert 'limit 1000000, consumed 1000000, requested 1' in artifact('helper-ci39119984084-failed.log.gz')
full=artifact('fresh-complete-projected-3.log.gz')
assert 'limit 10000000, consumed 9983347, requested 16654' in full
assert '1h 1min 52.765s' in full and 'status=1/FAILURE' in full
assert 'complete literal acceptance checked' not in artifact('fresh-complete-projected-3-progress.log.gz')
assert record['full_source_accepted'] is False
assert len(artifact('source-selection-expanded-targets.txt.gz').splitlines())==35
print('Verified7sources/10artifacts; source-selection proof audits pass; prior CI and full-source failures retained')
