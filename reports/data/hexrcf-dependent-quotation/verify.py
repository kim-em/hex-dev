#!/usr/bin/env python3
"""Verify dependent-quotation evidence, committed sources and retained failures."""
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

def read_log(path):
    return gzip.decompress((root / path).read_bytes()).decode()

assert git('rev-parse', record['source_commit'] + '^{tree}').decode().strip() == record['source_tree']
for path, expected in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + path)) == expected, path
    if args.check_head:
        assert sha((repo / path).read_bytes()) == expected, path
if args.check_head:
    changed = git('diff', '--name-only', record['source_commit']).decode().splitlines()
    untracked = git('ls-files', '--others', '--exclude-standard').decode().splitlines()
    assert all(path.startswith('reports/') for path in changed + untracked), changed + untracked
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git(
        'show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in ['integration', 'render', 'browser']:
    text = read_log(record['validation'][key])
    assert 'status=0/SUCCESS' in text, key
    assert ('Saved public-packet desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
text = read_log(record['validation']['integration'])
for label, expected in record['audit_counts'].items():
    match = re.search(re.escape(label) + r' actual bodies: (\d+) theorems/(\d+) definitions; '
                      r'nonempty traces=(\d+)', text)
    assert match and list(map(int, match.groups())) == expected, label
for label in ['sign', 'polynomial', 'empty graph', 'node context', 'moment context']:
    assert 'public packet compiled rejection/quotation refusal/caller restoration: ' + label in text
for name, nodes in [('reader', 1036), ('nested', 2196), ('continued', 1527),
                    ('queried', 763), ('boolReader', 595), ('multiple', 842), ('independent', 1084)]:
    assert f'dependent major checked Hex.RCF.DependentQuote.{name}; nodes={nodes};' in text
assert 'literal Booleans bypass the callback' in text
for name, nodes in [('reader', 10035), ('nested', 19984)]:
    assert f'dependent scalar original reader checked Hex.RCF.DependentScalarQuote.{name}; nodes={nodes}' in text
assert 'ordinary module sign packet proofNodes=861536' in text
assert 'coefficient from public packet; proofNodes=3249' in text
for module, expected in record['body_scope'].items():
    source = git('show', record['source_commit'] + ':' + module).decode()
    scope = re.search(r'let allowed := #\[(.*?)\]', source, re.S)
    assert scope and re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == expected, module
metadata = json.loads((root / 'validation' / 'metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = read_log('validation/memory-policy.txt.gz')
assert all(item in memory for item in ['ActiveState=active', 'MemoryMax=34359738368',
                                     'MemorySwapMax=0', 'OOMPolicy=kill'])
negative = read_log('diagnostics/multi-codec-context-probe-6.log.gz')
assert all(name in negative for name in ['Context.signPoly=1', 'Descriptor.prepareQueries=2', 'Element.codec=1'])
prototype = read_log('diagnostics/multi-codec-context-probe-7.log.gz')
assert 'status=0/SUCCESS' in prototype and 'codec transport producer reduction:' not in prototype
assert 'weekly limit' in read_log('diagnostics/public-packet-review-fix-opus-3.log.gz')
print(f"Verified {len(record['artifacts'])} artifacts, {len(record['sources'])} source files, "
      f"three fresh body audits, seven synthetic readers and two actual-codec readers")
