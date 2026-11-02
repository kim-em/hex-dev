#!/usr/bin/env python3
"""Verify retained root/header sources, validation, controls and body scope."""
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

def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=repo)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def log(key):
    return gzip.decompress((root / record['validation'][key]).read_bytes()).decode()

assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, expected in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == expected, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == expected, path
if args.check_head:
    changed = git('diff', '--name-only', record['source_commit']).decode().splitlines()
    untracked = git('ls-files', '--others', '--exclude-standard').decode().splitlines()
    assert all(path.startswith('reports/') for path in changed + untracked), changed + untracked
    assert sha((repo / 'reports/hexrcf-root-header-quotation.md').read_bytes()) == record['report_sha256']
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git(
        'show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in ['integration', 'budget', 'render', 'browser']:
    text = log(key)
    assert 'status=0/SUCCESS' in text, key
    assert ('Saved root-header desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
text = log('integration')
match = re.search(r'root/header packet actual bodies: (\d+) theorems/(\d+) definitions; '
                  r'nonempty traces=(\d+)', text)
assert match and list(map(int, match.groups())) == record['audit_counts']
for label in ['sign', 'polynomial', 'empty graph', 'node context', 'moment context']:
    assert 'public packet compiled rejection/quotation refusal/caller restoration: ' + label in text
for name in ['wrongVersion', 'wrongCount']:
    assert 'generic header rejection and caller restoration checked: Hex.RCF.RootQuoteTests.' + name in text
for name in ['readFirst', 'readSecond']:
    assert f'default signature exact subject: Hex.RCF.SignatureRoundtrip.{name}; nodes=160;' in text
assert 'generic header exact/one-below budgets checked; nodes=215671' in text
assert 'original root/header assembled; nodes=215734' in text
assert 'ordinary module sign packet proofNodes=860309' in text
assert 'coefficient from public packet; proofNodes=3249' in text
assert 'Built HexManual' in text
source = git('show', record['source_commit'] + ':conformance/HexRCF/RootHeaderProofs.lean').decode()
scope = re.search(r'let allowed := #\[(.*?)\]', source, re.S)
assert scope and re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == record['body_scope']
for legacy in ['root_raw', 'subject_read', 'nativeRoot_read']:
    assert '``Hex.RCF.RootQuoteTests.' + legacy in source
budget_source = git('show', record['source_commit'] + ':conformance/HexRCF/RootHeaderBudget.lean').decode()
assert 'result.root.usage == (← get).budget.consumed' in budget_source
assert 'source == ``RootQuoteTests.wrongCount && (← visits.get) == 0' in budget_source
assert 'generic header exact/one-below budgets checked; nodes=215671' in log('budget')
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = gzip.decompress((root / 'validation/memory-policy.txt.gz').read_bytes()).decode()
assert all(value in memory for value in ['ActiveState=active', 'MemoryMax=34359738368',
                                       'MemorySwapMax=0', 'OOMPolicy=kill'])
inspection = json.loads((root / 'captures/root-header-inspection.json').read_text())
assert {(item['label'], item['kind']) for item in inspection} == {
    ('desktop', 'value'), ('desktop', 'boundary'), ('narrow', 'value'), ('narrow', 'boundary')}
assert all(item['descendantOverflow'] <= 1 for item in inspection)
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources, "
      f"665/65/720 fresh bodies, header/signature budgets, five packet controls and four captures")
