#!/usr/bin/env python3
"""Verify native context sources, validation, controls and body scope."""
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
    assert sha((repo / 'reports/hexrcf-root-context.md').read_bytes()) == record['report_sha256']
    for path, expected in record['reports'].items():
        assert sha((repo / path).read_bytes()) == expected, path
for path in record['unchanged_guards']:
    assert git('show', record['baseline_commit'] + ':' + path) == git(
        'show', record['source_commit'] + ':' + path), path
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']
    if 'uncompressed_sha256' in item:
        assert sha(gzip.decompress(raw)) == item['uncompressed_sha256'], item['path']
for key in ['integration', 'manual', 'controls', 'render', 'browser']:
    text = log(key)
    assert 'status=0/SUCCESS' in text, key
    assert ('Saved root-context desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
text = log('integration')
match = re.search(r'root context actual bodies: (\d+) theorems/(\d+) definitions; '
                  r'nonempty traces=(\d+)', text)
assert match and list(map(int, match.groups())) == record['audit_counts']
for prefix, key in [('root/header packet', 'header_counts'), ('frozen signature', 'signature_counts')]:
    match = re.search(re.escape(prefix) + r' actual bodies: (\d+) theorems/(\d+) definitions; '
                      r'nonempty traces=(\d+)', text)
    assert match and list(map(int, match.groups())) == record[key]
assert 'public scalar graph retains frozen numerical node and nested-moment signatures' in text
assert 'ordinary module sign packet proofNodes=904273' in text
for name, nodes in [('readFirst', 254), ('readSecond', 254), ('readProjected', 427)]:
    assert f'frozen signature exact subject and exact/one-below budgets: Hex.RCF.FrozenSignature.{name}; nodes={nodes}' in text
for name, binding in [('first', 'second_literal'), ('second', 'first_literal')]:
    assert f'wrong frozen signature binding/subject rejected and caller restored: Hex.RCF.FrozenSignature.{name}/Hex.RCF.FrozenSignature.{binding}' in text
assert 'different frozen signature payload declines; a later exact quotation succeeds' in text
packet = git('show', record['source_commit'] + ':conformance/HexRCF/RootHeaderPacket.lean').decode()
assert 'evidence.getUsedConstants.all constructors.contains' in packet
assert 'mkRawNatLit' in packet and 'graphExpr' not in packet
signature = git('show', record['source_commit'] + ':conformance/HexRCF/FrozenSignatureProofs.lean').decode()
assert 'theorems == 23 && definitions == 7 && traces == 16' in signature
assert '#[``Tower.rootData,``Dag.encode]' in signature
assert 'dependencies.contains ``Tower.Signature.codec_literal' in signature
for label in ['sign', 'polynomial', 'empty graph', 'node context', 'moment context']:
    assert 'public packet compiled rejection/quotation refusal/caller restoration: ' + label in text
for message in [
    'native context packing exact/one-below budget checked; proofNodes=2653',
    'packed ordinary-real model retains the exact selected coefficient value and positive sign',
    'wrong native parent rejects and restores caller assignments and declarations',
    'unresolved native root rejects without assigning caller metavariables']:
    assert message in text and message in log('controls'), message
assert 'Built HexManual' in log('manual')
source = git('show', record['source_commit'] + ':conformance/HexRCF/RootContextProofs.lean').decode()
scope = re.search(r'let allowed := #\[(.*?)\]', source, re.S)
assert scope and re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)) == record['body_scope']
assert '#[``Tower.rootData,``Dag.encode]' in source
for legacy in ['root_raw', 'subject_read', 'nativeRoot_read']:
    assert '``Hex.RCF.RootQuoteTests.' + legacy in source
cases = git('show', record['source_commit'] + ':conformance/HexRCF/RootContextConformance.lean').decode()
assert 'result.usage == (← get).budget.consumed' in cases
assert 'RealModel.build' in cases and 'Tower.Model.root_value' in cases
assert 'addNoncomputable' in cases and 'compileDecl declaration' in cases
assert '2653' not in cases, 'Budget must be derived, not hard-coded'
manual = git('show', record['source_commit'] + ':HexManual/Chapters/HexRCF/RootQuote.lean').decode()
assert 'Model\nconstruction is checked separately' in manual
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = gzip.decompress((root / 'validation/memory-policy.txt.gz').read_bytes()).decode()
assert all(value in memory for value in ['ActiveState=active', 'MemoryMax=34359738368',
                                       'MemorySwapMax=0', 'OOMPolicy=kill'])
inspection = json.loads((root / 'captures/root-context-inspection.json').read_text())
assert {(item['label'], item['kind']) for item in inspection} == {
    ('desktop', 'signature'), ('desktop', 'value'), ('desktop', 'boundary'),
    ('narrow', 'signature'), ('narrow', 'value'), ('narrow', 'boundary')}
assert all(item['descendantOverflow'] <= 1 for item in inspection)
section = json.loads((root / 'captures/root-context-section-overflow.json').read_text())
assert {row['width'] for row in section} == {1440, 390}
assert all(target['overflow'] <= 1 for row in section for target in row['targets'])
document = json.loads((root / 'captures/root-context-document.json').read_text())
assert document['currentPacket'] and document['currentTransport'] and document['currentFrozen']
assert document['cubicSource'] == 'https://github.com/kim-em/hex-dev/blob/main/conformance/HexRCF/RootQuoteSource.lean'
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources, "
      f"682/68/735 fresh bodies, 674/66/725 header bodies and 23/7/16 signature bodies, packing budgets/restoration, five packet controls and six captures")
