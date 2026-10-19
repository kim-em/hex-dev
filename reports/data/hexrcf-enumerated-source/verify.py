#!/usr/bin/env python3
"""Verify source-bound enumerated-source production and independent replay evidence."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check-head', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parents[2]
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
record = json.loads((root / 'context.json').read_text())
parent = root.parent / 'hexrcf-admission'
subprocess.run([sys.executable, str(parent / 'verify.py')], check=True)
assert sha((parent / 'context.json').read_bytes()) == record['parent_context_sha256']
for name, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + name)) == digest, name
    if args.check_head:
        assert sha((repo / name).read_bytes()) == digest, name
for item in record['artifacts']:
    data = (root / item['path']).read_bytes()
    assert len(data) == item['bytes'] and sha(data) == item['sha256'], item['path']

def log(name):
    return gzip.decompress((root / (name + '.gz')).read_bytes()).decode()

for name in ['source-build-controls-3.log', 'source-build-inputs-2.log',
             'source-build-quote-3.log', 'source-build-audit-2.log',
             'source-build-integration-3.log', 'source-build-render-2.log']:
    assert 'Build completed successfully' in log(name), name
    assert 'code=exited, status=0/SUCCESS' in log(name), name
quoted = log('source-build-quote-3.log')
for name, count in zip(['positive', 'negative', 'cubic'], record['proof_nodes']):
    assert f'EnumeratedSourceQuote.{name}: proofNodes={count}' in quoted
assert '1488 theorems/865 definitions; nonempty traces=2323' in log('source-build-audit-2.log')
assert '1488 theorems/865 definitions; nonempty traces=2323' in log('source-build-integration-3.log')
assert 'proofNodes=8651669' in log('source-build-integration-3.log')
assert 'limit 1000000, consumed 1000000, requested 1' in log('source-build-quote-1.log')
invocation = json.loads((root / 'source-build-integration-invocation.json').read_text())
assert invocation['targets'] == 54
for target in ['HexManual', 'HexRCFRealCoefficients', 'HexRCF.SourceBuild',
               'HexRCF.EnumeratedSource.Proofs', 'HexRCF.CellSourceProofs',
               'HexRCF.HandlerTests.Async', 'HexRCF.SourceIdentityEmit']:
    assert target in invocation['argv'], target
source = lambda name: git('show', record['source_commit'] + ':' + name).decode()
previous = lambda name: git('show', record['base_commit'] + ':' + name).decode()
guard = source('conformance/HexRCF/SelectedRoot/KernelCheck.lean')
old = previous('conformance/HexRCF/SelectedRoot/KernelCheck.lean')
guard = guard.replace('import HexRCF.RealCoefficients.SourceBuild\n', '')
guard = guard.replace('``Descriptor.prepareQueries,\n'
    '    -- Literal names keep native adapter production out of proof-only imports.\n'
    '    `Hex.RCF.RealCoefficients.SourceBuild.build,\n'
    '    `Hex.RCF.RealCoefficients.SourceBuild.select,\n'
    '    `Hex.RCF.RealCoefficients.ScalarPacket.buildParts]', '``Descriptor.prepareQueries]')
assert guard == old, 'The shared producer guard has changes beyond the three additions'
packet = source('adapters/HexRCF/RealCoefficients/ScalarPacket.lean')
old = previous('adapters/HexRCF/RealCoefficients/ScalarPacket.lean')
marker = '/-- Read exactly the supplied polynomial, sign and graph.'
assert packet[packet.index(marker):] == old[old.index(marker):], 'Scalar replay changed'
assert source('HexRCF/Tactic.lean') == previous('HexRCF/Tactic.lean')
metadata = json.loads((root / 'source-build-metadata.json').read_text())
assert len(metadata) == 9 and all(x['exit_code'] == 0 for x in metadata)
progress = log('source-build-progress-controls-1.log')
for name in ['buildParts_success', 'build_success']:
    assert f'actual scalar production progress Hex.RCF.RealCoefficients.ScalarPacket.{name}' in progress
integration_sources = json.loads((root / 'source-build-integration-sources.json').read_text())['sources']
assert integration_sources == record['integration_sources']
changed = [name for name, digest in integration_sources.items() if record['sources'][name] != digest]
assert changed == record['manual_changes'] == ['HexManual/Chapters/HexRCF/AlgebraicCells.lean']
before = (root / 'failed-browser-attempt-1/AlgebraicCells.lean.before-layout.txt').read_bytes()
assert sha(before) == integration_sources[changed[0]]
assert 'Id.run do' in source(changed[0]) and 'SourceBuild.build' in source(changed[0])
inspections = json.loads((root / 'source-build-final-inspection.json').read_text())
assert {(x['label'], x['kind']) for x in inspections} == {
    (width, kind) for width in ['desktop', 'narrow'] for kind in ['api', 'apicode', 'source']}
assert all(x['descendantOverflow'] <= 1 and x['targetScrollWidth'] <= x['targetWidth'] + 1
           for x in inspections)
viewed = json.loads((root / 'source-build-viewed.json').read_text())
assert len(viewed['viewed']) == 6 and viewed['all_changed_targets_readable']
policy = (root / 'run-bounded.txt').read_text()
assert all(text in policy for text in ['MemoryMax=32G', 'MemorySwapMax=0', 'LEAN_NUM_THREADS=2'])
print(f"Verified enumerated-source evidence: {len(record['sources'])} source bindings, "
      f"{len(record['artifacts'])} artifacts, three independent identities, "
      "1488/865/2323 fresh audit, 54 targets and six inspected captures; full #10358 incomplete")
