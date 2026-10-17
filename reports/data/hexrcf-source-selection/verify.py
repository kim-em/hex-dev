#!/usr/bin/env python3
"""Verify retained artifacts and their recorded committed source bytes."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import argparse

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true',
    help='also require HEAD and tracked worktree changes after the recorded source to be reports only')
args = parser.parse_args()

root = Path(__file__).resolve().parent
repo = root.parents[2]
record = json.loads((root / 'context.json').read_text())
sha = lambda data: hashlib.sha256(data).hexdigest()
for entry in record['artifacts']:
    raw = (root / entry['path']).read_bytes()
    assert len(raw) == entry['bytes'], entry['path']
    assert sha(raw) == entry['sha256'], entry['path']
    if 'uncompressed_sha256' in entry:
        assert sha(gzip.decompress(raw)) == entry['uncompressed_sha256'], entry['path']
for path, expected in record['sources'].items():
    raw = subprocess.check_output(['git', 'show', record['source_commit'] + ':' + path], cwd=repo)
    assert sha(raw) == expected, path
validation = record['validation']
for name in ['integration', 'render', 'browser']:
    text = gzip.decompress((root / validation[name]).read_bytes()).decode()
    assert 'status=0/SUCCESS' in text, name
    if name == 'browser':
        assert 'Saved source-selection desktop/narrow screenshots' in text
    else:
        assert 'Build completed successfully' in text, name
text = gzip.decompress((root / validation['integration']).read_bytes()).decode()
match = re.search(r'source-selection inspection: (\d+) theorem bodies/(\d+) definitions; (\d+) nonempty traces', text)
assert match
assert list(map(int, match.groups())) == list(validation['audit'].values())
assert f"source selection: {validation['generic_bodies']} exported theorem bodies" in text
cancelled = gzip.decompress((root / record['render_cancelled']['log']).read_bytes()).decode()
assert 'status=15/TERM' in cancelled
assert 'Build completed successfully' not in cancelled
failed = json.loads((root / record['failed_browser']['artifacts'] /
    'source-selection-section-overflow.json').read_text())
measured = max(target['overflow'] for viewport in failed for target in viewport['targets'])
assert measured == record['failed_browser']['overflow_pixels']
if args.check_head:
    for arguments in [
            ['diff', '--name-only', record['source_commit'], 'HEAD'],
            ['diff', '--name-only', 'HEAD']]:
        changed = subprocess.check_output(['git', *arguments], cwd=repo, text=True).splitlines()
        assert all(path.startswith('reports/') for path in changed), changed
print(f"Verified {len(record['artifacts'])} artifacts and {len(record['sources'])} committed sources")
