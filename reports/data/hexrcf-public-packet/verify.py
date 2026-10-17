#!/usr/bin/env python3
"""Verify retained public-packet evidence against its committed sources."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[2]
record = json.loads((root / 'context.json').read_text())


def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo)


def sha(data):
    return hashlib.sha256(data).hexdigest()


assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, expected in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == expected, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == expected, path
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git(
        'show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']


def log(key):
    return gzip.decompress((root / record['validation'][key]).read_bytes()).decode()


for key in ['integration', 'render', 'browser']:
    text = log(key)
    assert 'status=0/SUCCESS' in text, key
    assert ('Saved public-packet desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
text = log('integration')
audit = re.search(r'public packet actual bodies: (\d+) theorems/(\d+) definitions; '
                  r'nonempty traces=(\d+)', text)
assert audit and list(map(int, audit.groups())) == record['audit_counts']
for label in ['sign', 'polynomial', 'empty graph', 'node context', 'moment context']:
    assert 'public packet compiled rejection/quotation refusal/caller restoration: ' + label in text
for nodes in [903, 1845]:
    assert f'nodes={nodes}; axioms=[propext]' in text
assert 'ordinary module sign packet proofNodes=823379' in text
assert 'coefficient from public packet; proofNodes=3249' in text
source = git('show', record['source_commit'] +
             ':conformance/HexRCF/PublicSignPacketProofs.lean').decode()
scope = re.search(r'let allowed := #\[(.*?)\]', source, re.S)
assert scope and re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == record['body_scope']
metadata = json.loads((root / record['validation']['metadata']).read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = gzip.decompress((root / record['validation']['memory']).read_bytes()).decode()
assert all(item in memory for item in ['ActiveState=active', 'MemoryMax=34359738368',
                                     'MemorySwapMax=0', 'OOMPolicy=kill'])
print(f"Verified {len(record['artifacts'])} artifacts, {len(record['sources'])} committed sources, "
      f"audit {record['audit_counts']}, five packet controls and bounded validation.")
