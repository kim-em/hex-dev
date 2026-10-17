#!/usr/bin/env python3
"""Verify proof-input function transport and source-bound validation."""
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
for key in ['integration', 'ci_fix', 'render', 'browser']:
    text = log(key)
    assert 'code=exited, status=0/SUCCESS' in text, key
    assert ('Saved root preparation desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, key
integration = log('integration')
assert 'Built HexManual' in integration
for message in [
    'proofFunction; nodes=1079; axioms=[]',
    'continuedFunction; nodes=1099; axioms=[]',
    'dependent quotation actual bodies: 145 theorems/16 definitions; nonempty traces=88',
    'retained root/context actual bodies: 807 theorems/63 definitions; nonempty traces=855',
    'dependent scalar actual bodies: 61 theorems/4 definitions; nonempty traces=56',
    'public packet actual bodies: 692 theorems/67 definitions; nonempty traces=749',
    'root/header packet actual bodies: 710 theorems/66 definitions; nonempty traces=761',
    'root context actual bodies: 718 theorems/68 definitions; nonempty traces=771']:
    assert message in integration, message
assert 'root-table quotation: 94 theorem bodies, 14 data definitions' in log('ci_fix')
assert 'complete standard-three axiom closure; no native producer reductions' in log('ci_fix')
core = source('adapters/HexRCF/RealCoefficients/RootQuote.lean')
assert 'private def proofFunction?' in core
assert 'unless ← isProp proofType do return none' in core
assert 'body.hasLooseBVars' in core
assert 'mkAppM ``Eq.mpr #[equality,proof]' in core
assert 'Hex.RCF.checkProof `RootQuote.majorTransport kind value' in core
controls = source('conformance/HexRCF/DependentQuote.lean')
assert '``Hex.RCF.DependentQuote.dependentData,``Hex.RCF.DependentQuote.dependentFunction' in controls
assert 'result.usage.proofNodes-1' in controls and 'refused "non-proof argument"' in controls
public = source('conformance/HexRCF/ProofFunctionPublic.lean')
assert 'public import HexRCF.DependentQuote' in public and 'import all' not in public
assert 'continuedFunction = some 29' in public
audit = source('conformance/HexRCF/DependentQuoteProofs.lean')
assert '``Hex.RCF.ProofFunctionPublic.first,``Hex.RCF.ProofFunctionPublic.continued' in audit
assert 'theorems == 145 && definitions == 16 && traces == 88' in audit
assert 'KernelCheck.violation?' in audit and 'AxiomClosure.collect roots' in audit
metadata = json.loads((root / 'validation/metadata.json').read_text())
assert {item['name'] for item in metadata} == {
    'copyright', 'lines', 'dag', 'admissions', 'selected-admissions', 'relative', 'diff'}
assert all(item['exit_code'] == 0 for item in metadata)
memory = gzip.decompress((root / 'validation/memory-policy.txt.gz').read_bytes()).decode()
assert all(value in memory for value in ['ActiveState=active', 'MemoryMax=34359738368',
                                       'MemorySwapMax=0', 'OOMPolicy=kill', 'LEAN_NUM_THREADS=2'])
inspection = json.loads((root / 'captures/inspection.json').read_text())
assert {(item['label'], item['kind']) for item in inspection} == {
    (label, kind) for label in ['desktop', 'narrow'] for kind in ['introduction', 'example', 'budget']}
assert all(item['descendantOverflow'] <= 1 and item['targetScrollWidth'] <= item['targetWidth']+1
           for item in inspection)
assert len(record['visually_inspected_captures']) == 6
assert record['complete_packet_accepted'] is False
for key in ['diagnostics/fresh-complete-frozen-3.log.gz',
            'diagnostics/fresh-complete-frozen-4.log.gz',
            'diagnostics/fresh-complete-frozen-5.log.gz']:
    text = gzip.decompress((root / key).read_bytes()).decode()
    assert 'budget exhausted in dimension proof nodes' in text
print(f"Verified {len(record['artifacts'])} artifacts/{len(record['sources'])} sources; "
      '145/16/88 function bodies, 94/14 root-table bodies, compatibility, manual and six captures')
