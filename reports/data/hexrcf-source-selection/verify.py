#!/usr/bin/env python3
"""Verify retained artifacts and their recorded committed source bytes."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess

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
print(f"Verified {len(record['artifacts'])} artifacts and {len(record['sources'])} committed sources")
