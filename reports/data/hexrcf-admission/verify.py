#!/usr/bin/env python3
"""Verify the source-bound admission traversal evidence and immutable parent."""
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
sha = lambda raw: hashlib.sha256(raw).hexdigest()
git = lambda *a: subprocess.check_output(['git', *a], cwd=repo)
record = json.loads((root / 'context.json').read_text())
parent = root.parent / 'hexrcf-cell-finish' / 'rollback'
subprocess.run([sys.executable, str(parent / 'verify.py')], check=True)
assert sha((parent / 'context.json').read_bytes()) == record['parent_context_sha256']
changed = git('diff', '--name-only', record['base_commit'],
              record['source_commit']).decode().splitlines()
assert sorted(changed) == sorted([
    'HexRCF/Tactic.lean', 'HexRCF/HandlerTests/Admission.lean', 'lakefile.lean'])
for name, digest in record['sources'].items():
    assert sha(git('show', record['source_commit'] + ':' + name)) == digest, name
    if args.check_head:
        assert sha((repo / name).read_bytes()) == digest, name
for item in record['artifacts']:
    raw = (root / item['path']).read_bytes()
    assert len(raw) == item['bytes'] and sha(raw) == item['sha256'], item['path']

def log(name):
    return gzip.decompress((root / (name + '.gz')).read_bytes()).decode()

for name in ['axiom-forest-full-1.log', 'axiom-forest-audit-1.log',
             'axiom-forest-admission-2.log', 'axiom-forest-integration-1.log']:
    assert 'Build completed successfully' in log(name), name
    assert 'code=exited, status=0/SUCCESS' in log(name), name
assert 'proofNodes=8651669' in log('axiom-forest-full-1.log')
assert '1193 theorems/202 definitions; nonempty traces=1353' in log('axiom-forest-audit-1.log')
assert 'forest/reference agree on 19' in log('axiom-forest-admission-2.log')
assert 'forest admission follows all three rolled-back environments' in log('axiom-forest-admission-2.log')
assert 'declaration uses `sorry`' not in log('axiom-forest-admission-2.log')
invocation = json.loads((root / 'axiom-forest-integration-invocation.json').read_text())
assert invocation['targets'] == 51
for target in ['HexRCF.CellSourceProofs', 'HexRCF.HandlerTests.Admission',
               'HexRCF.HandlerTests.Async', 'HexRCF.ReifyTests', 'HexManual',
               'HexRCFRealCoefficients']:
    assert target in invocation['argv'], target
assert all(item['exit_code'] == 0 for item in record['metadata'])
samples = log('axiom-forest-cost-1.log')
for trial, arm, elapsed in [(0, 'A', 20073555), (0, 'B', 5839078),
                            (1, 'B', 5572483), (1, 'A', 19694513)]:
    assert f'trial={trial}; arm={arm}; ns={elapsed}; repetitions=10; depth=128; roots=8' in samples
checker = git('show', record['source_commit'] + ':HexRCF/Tactic.lean').decode()
proof_check = checker.split('meta def checkProof ', 1)[1].split('private meta def dispatchHandlers', 1)[0]
assert proof_check.count('checkAxioms name proof') == 2
assert 'hasUnsafe proof' in proof_check and '(cache := false)' in proof_check
assert 'debug.skipKernelTC.set' in proof_check and 'isDefEq' in proof_check
assert 'MemoryMax=32G' in (root / 'run-bounded.txt').read_text()
assert 'MemorySwapMax=0' in (root / 'run-bounded.txt').read_text()
assert 'LEAN_NUM_THREADS=2' in (root / 'run-bounded.txt').read_text()
policy = (root / 'axiom-forest-integration-memory-policy.txt').read_text()
assert 'ActiveState=active' in policy
assert 'MemoryMax=34359738368' in policy and 'MemorySwapMax=0' in policy
print(f"Verified admission evidence: {len(record['sources'])} source bindings, "
      f"{len(record['artifacts'])} artifacts, 51-target integration, 19+3 policy cases; "
      "guard-only paired costs, not a whole-tactic speedup")
