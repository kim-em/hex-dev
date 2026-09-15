#!/usr/bin/env python3
"""Isolate kernel powering and table lookup costs using adjacent fresh builds.

The powDiv diagnostic follows PrimeCert/PowMod.lean by Bhavik Mehta,
Copyright (c) 2022 Bhavik Mehta, licensed under Apache 2.0.
"""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import run

HEADER = '''module
public import HexPrimality.Cert
public section
set_option maxRecDepth 100000
'''
RAW = '''
@[expose] noncomputable def powBits (a e n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ acc _ => acc)
    (fun _ r bit acc base =>
      (e.testBit bit).rec
        (r (bit.add 1) acc ((base.mul base).mod n))
        (r (bit.add 1) ((acc.mul base).mod n) ((base.mul base).mod n)))
    (HexArith.bitLength e) 0 (1 % n) (a % n)

@[expose] noncomputable def powDiv (a e n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun _ _ _ => 0)
    (fun _ r base exp acc =>
      (exp.beq 0).rec
        (((exp.mod 2).beq 0).rec
          (r ((base.mul base).mod n) (exp.div 2) ((acc.mul base).mod n))
          (r ((base.mul base).mod n) (exp.div 2) acc))
        (acc.mod n))
    e.succ (a % n) e 1
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cpu = pick()
    p = 2**255-19
    arms = {'baseline': '',
            'current-power': f'example : HexArith.powModNat 2 {p-1} {p} = 1 := by decide +kernel\n',
            'raw-bits': f'example : powBits 2 {p-1} {p} = 1 := by decide +kernel\n',
            'raw-div': f'example : powDiv 2 {p-1} {p} = 1 := by decide +kernel\n',
            'table': 'example : Hex.Nat.isTablePrime 57467 = true := by decide +kernel\n'}
    module = 'HexPrimality.ProofProbe.Curve25519.KernelDiagnostic'
    source = ROOT/'bench'/Path(module.replace('.', '/')+'.lean')
    artifact = ROOT/'.lake/build/lib/lean'/Path(module.replace('.', '/')+'.olean')
    output = args.output
    record = {'cpu': cpu, 'samples': [], 'protocol': 'two reversed blocks; all completed samples retained'}
    if source.exists() or output.exists():
        raise RuntimeError('refusing to overwrite a probe or retained record')
    try:
        for block in range(2):
            for arm in (list(arms) if block == 0 else list(reversed(arms))):
                body = HEADER+RAW+arms[arm]
                source.write_text(body)
                artifact.unlink(missing_ok=True)
                row = run(['lake', 'build', '+'+module+':olean'], ROOT, 60, cpu)
                row.update(block=block, arm=arm, source=body)
                record['samples'].append(row)
                output.write_text(json.dumps(record, indent=2)+'\n')
                print(block, arm, row['status'], row['seconds'], flush=True)
                if row['status'] != 'ok':
                    raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        source.unlink(missing_ok=True)

if __name__ == '__main__':
    main()
