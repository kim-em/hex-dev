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
assert subprocess.check_output(['git', 'rev-parse', record['source_commit'] + '^{tree}'],
    cwd=repo, text=True).strip() == record['source_tree']
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
changed = subprocess.check_output(['git', 'diff', '--name-only',
    'origin/main...' + record['source_commit']], cwd=repo, text=True).splitlines()
assert all(path.startswith('reports/') or path in record['sources'] for path in changed), changed
kernel = subprocess.check_output(['git', 'show', record['source_commit'] +
    ':conformance/HexRCF/SourceSelectionKernel.lean'], cwd=repo, text=True)
scope = re.search(r'unless #\[(.*?)\]\.contains modules\[index\]!', kernel, re.S)
assert scope
assert re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == record['body_scope']
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
fresh = gzip.decompress((root / validation['fresh_audit']).read_bytes()).decode()
assert 'status=0/SUCCESS' in fresh
fresh_match = re.search(r'source-selection inspection: (\d+) theorem bodies/(\d+) definitions; (\d+) nonempty traces', fresh)
assert fresh_match and fresh_match.groups() == match.groups()
for label, nodes in validation['quotation_nodes'].items():
    assert re.search(re.escape(label) + r' proofNodes=' + str(nodes) + r'\b', text), label
report = (repo / 'reports/hexrcf-source-selection.md').read_text()
counts = validation['audit']
assert f"rechecks {counts['theorem_bodies']} reachable theorem bodies and {counts['definitions']} definitions" in report
assert f"{counts['nonempty_traces']} checks have" in report
assert f"rechecks {validation['generic_bodies']} exported theorem bodies" in report
for nodes in validation['quotation_nodes'].values():
    assert re.search(r'(?<![\d,])' + re.escape(f'{nodes:,}') + r'(?![\d,])', report), nodes
cancelled = gzip.decompress((root / record['render_cancelled']['log']).read_bytes()).decode()
assert 'status=15/TERM' in cancelled
assert 'Build completed successfully' not in cancelled
failed = json.loads((root / record['failed_browser']['artifacts'] /
    'source-selection-section-overflow.json').read_text())
measured = max(target['overflow'] for viewport in failed for target in viewport['targets'])
assert measured == record['failed_browser']['overflow_pixels']
subprocess.run(['python3', str(root / 'scripts/check-negative-fixture.py'),
    str(root / 'logs/source-selection-negative-emitter-1.log.gz'),
    str(repo / 'conformance-fixtures/HexRCF/source-selection-negative.json')], check=True)
if args.check_head:
    subprocess.run(['git', 'merge-base', '--is-ancestor', record['source_commit'], 'HEAD'],
        cwd=repo, check=True)
    for arguments in [
            ['diff', '--name-only', record['source_commit'], 'HEAD'],
            ['diff', '--name-only', 'HEAD']]:
        changed = subprocess.check_output(['git', *arguments], cwd=repo, text=True).splitlines()
        assert all(path.startswith('reports/') for path in changed), changed
print(f"Verified {len(record['artifacts'])} artifacts and {len(record['sources'])} committed sources")
