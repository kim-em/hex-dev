#!/usr/bin/env python3
"""Compare list-backed table search with verified bit lookup in kernel replay."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import run

HEADER = '''module
public import HexPrimality.Cert
public section
set_option maxRecDepth 100000
open Hex.Nat
mutual
@[expose] def oldCheck : PrimeCert → Bool
  | .small n => tableSearch n
  | .pock n fs => checkPockArith n fs && oldChildren fs
  | .pock3 n r s w fs => checkPock3Arith n r s w fs && oldChildren fs
  | .pock3Sieve n r s w m fs => checkPock3SieveArith n r s w m fs && oldChildren fs
@[expose] def oldChildren : List (Nat × Nat × PrimeCert) → Bool
  | [] => true
  | (_, _, c) :: cs => oldCheck c && oldChildren cs
end
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cpu = pick()
    literal = (ROOT/'bench/HexPrimality/ProofProbe/Curve25519/Literal.lean').read_text()
    certificate = literal.split('def certificate : Hex.Nat.PrimeCert :=')[1].split('\nend ')[0]
    common = HEADER+'\ndef certificate : PrimeCert :=\n'+certificate+'\n'
    pairs = [('lookup', 'tableSearch 57467', 'isTablePrime 57467'),
             ('certificate', 'oldCheck certificate', 'checkPrime certificate')]
    module = 'HexPrimality.ProofProbe.Curve25519.TableReplay'
    source = ROOT/'bench'/Path(module.replace('.', '/')+'.lean')
    artifact = ROOT/'.lake/build/lib/lean'/Path(module.replace('.', '/')+'.olean')
    output = args.output
    record = {'cpu': cpu, 'host': platform.node(), 'samples': [],
              'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'], cwd=ROOT)).hexdigest(),
              'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
              'source_sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                                for name in ('HexPrimality/Table.lean', 'HexPrimality/Sieve.lean', 'HexPrimality/Cert.lean')},
              'table_sha256': hashlib.sha256((ROOT/'HexPrimality/Table.lean').read_bytes()).hexdigest(),
              'protocol': 'two trial-major blocks; adjacent old/new arms reversed in second block; all completed samples retained'}
    if source.exists() or output.exists():
        raise RuntimeError('refusing to overwrite a probe or retained record')
    try:
        for block in range(2):
            for phase, old, new in pairs:
                for arm, term in ([('old', old), ('new', new)] if block == 0 else [('new', new), ('old', old)]):
                    body = common+f'example : ({term}) = true := by decide +kernel\n'
                    source.write_text(body)
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', '+'+module+':olean'], ROOT, 60, cpu)
                    row.update(block=block, phase=phase, arm=arm, source=body,
                               source_bytes=len(body.encode()),
                               olean_bytes=artifact.stat().st_size if artifact.exists() else None)
                    record['samples'].append(row)
                    output.write_text(json.dumps(record, indent=2)+'\n')
                    print(block, phase, arm, row['status'], row['seconds'], flush=True)
                    if row['status'] != 'ok':
                        raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        source.unlink(missing_ok=True)

if __name__ == '__main__':
    main()
