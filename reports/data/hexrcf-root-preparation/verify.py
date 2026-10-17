#!/usr/bin/env python3
"""Verify source-bound preparation proofs, controls and rendered examples."""
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

def source(path):
    return git('show', record['source_commit'] + ':' + path).decode()

def log(key):
    return gzip.decompress((root / record['validation'][key]).read_bytes()).decode()

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
for key in ['integration', 'controls', 'audit', 'render', 'browser']:
    text = log(key)
    assert 'code=exited, status=0/SUCCESS' in text, key
    assert ('Saved root preparation desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
integration = log('integration')
assert 'Built HexManual' in integration
assert 'full request proof budget=2383805' in integration
for prefix, expected in record['audit_counts'].items():
    pattern = re.escape(prefix) + r' actual bodies: (\d+) theorems/(\d+) definitions; nonempty traces=(\d+)'
    match = re.search(pattern, integration)
    assert match and list(map(int, match.groups())) == expected, prefix
assert '96 theorem bodies, 11 definitions' in integration
assert 'sign packet nonempty diagnostic traces: 97' in integration
assert 'actual cubic and conditional quotation bodies under kernel producer diagnostics: 256' in integration
assert 'generic rational quotation: 201 actual theorem bodies' in integration
assert 'standalone sign packet proofNodes=69973' in integration
assert 'ordinary module sign packet proofNodes=1168494' in integration
controls = log('controls')
assert 'exact/one-below request budget=2381262; caller state restored' in controls
assert 'wrong-sign rejection restored caller declarations and metavariables' in controls
for variant in range(3):
    assert f'malformed retained input refused with caller rollback: variant={variant}' in controls
audit = source('conformance/HexRCF/RootPrepareProofs.lean')
scope = re.search(r'let allowed := #\[(.*?)\]', audit, re.S)
assert scope and re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == record['body_scope']
assert '#[``Tower.rootData,``Dag.encode]' in audit
for legacy in ['root_raw', 'subject_read', 'nativeRoot_read']:
    assert '``Hex.RCF.RootQuoteTests.' + legacy in audit
core = source('adapters/HexRCF/RealCoefficients/RootPrepare.lean')
assert 'mkAuxDefinition declaration kind expression (compile := false)' in core
assert 'charge .proofNodes work.numSteps' in core
assert 'Meta.simpCore expression simpContext' in core and 'catch' not in core
public = source('conformance/HexRCF/RootPreparePublic.lean')
assert 'public import HexRCF.RootPreparePacket' in public and 'import all' not in public
assert 'RootPreparePacket.read_checked' in public
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = gzip.decompress((root / 'validation/memory-policy.txt.gz').read_bytes()).decode()
assert all(value in memory for value in ['ActiveState=active', 'MemoryMax=34359738368',
                                       'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
expected_captures = {(label, kind) for label in ['desktop', 'narrow']
                     for kind in ['introduction', 'example', 'budget']}
assert {(item['label'], item['kind']) for item in inspection} == expected_captures
assert all(item['descendantOverflow'] <= 1 and item['targetScrollWidth'] <= item['targetWidth'] + 1
           for item in inspection)
assert len(record['visually_inspected_captures']) == 6
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '807/63/855 preparation bodies, exact/below budgets and rollback, compatibility, manual and six captures')
