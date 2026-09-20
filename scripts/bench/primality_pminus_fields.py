#!/usr/bin/env python3
"""Reproduce the independent draft p−1 stage-2 comparison for issue #10362.

Use a disposable checkout of the pinned PR revision. The driver installs a
measurement-only probe there; all completed calls are retained. Production
sources and the checker are unchanged.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import corpus
from scripts.bench.primality_field_sweep import RESIDUALS

REVISION = 'af894cbb8fa86164ad8da113d9b26c5bc8bff76d'
PROBE = 'bench/HexPrimality/FieldProbe.lean'
EXTRA = '''  if let ["construction-pminus", nArg, enabled] := args then
    let some n := nArg.toNat? | return 2
    return ← runConstruction n 521 32 32768 false (enabled == "true")
  if let ["pminus", nArg, aArg, b1Arg, b2Arg] := args then
    let some [n, a, b₁, b₂] := [nArg, aArg, b1Arg, b2Arg].mapM String.toNat? | return 2
    let input ← IO.mkRef (n, a, b₁, b₂)
    let (n, a, b₁, b₂) ← input.get
    let begin ← IO.monoNanosNow
    let result ← IO.mkRef (PMinusOne.searchCounted n a b₁ b₂ (Hex.Rand.ofSeed n))
    let result ← result.get
    let finish ← IO.monoNanosNow
    if let .factor d := result.result then
      unless 1 < d && d < n && n % d == 0 do
        throw (IO.userError "invalid divisor")
    IO.println (Lean.Json.mkObj [
      ("nanos", Lean.toJson (finish - begin)),
      ("attempts", Lean.toJson result.attempts),
      ("result", Lean.toJson (reprStr result.result)),
      ("events", Lean.toJson (reprStr (result.events.map fun e => { e with batches := [] })))]).compress
    return 0
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    if args.output.exists():
        parser.error('output must not exist')
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    if revision != REVISION:
        parser.error(f'checkout must be at {REVISION}')
    source = subprocess.check_output(['git', 'show', f'HEAD:{PROBE}'], cwd=checkout, text=True)
    source = source.replace('(trace : Bool) : IO UInt32',
                            '(trace : Bool) (stage2 : Bool := false) : IO UInt32')
    source = source.replace('factor := { constructionBudget.factor with\n',
                            'factor := { constructionBudget.factor with\n        pMinusOneStage2 := stage2\n')
    source = source.replace('  if let "validate" ::', EXTRA + '  if let "validate" ::')
    (checkout / PROBE).write_text(source)
    subprocess.run(['lake', 'build', 'hexprimality_field_probe'], cwd=checkout, check=True)
    exe = checkout / '.lake/build/bin/hexprimality_field_probe'
    cpu = pick()
    record = dict(revision=revision, pull_request=10364, host=platform.node(), cpu=cpu,
                  probe_source=source, driver_source=Path(__file__).read_text(),
                  probe_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),
                  protocol='two trial-major blocks, adjacent AB/BA, every completed call retained',
                  residual_bounds=[(64, 4096), (32768, 524288), (524288, 4194304)],
                  bases=[2, 3], samples=[], completion='running')

    def save():
        args.output.write_text(json.dumps(record, indent=2) + '\n')

    def run(command, **metadata):
        load = os.getloadavg()
        result = subprocess.run(['taskset', '-c', str(cpu), str(exe), *map(str, command)],
                                cwd=checkout, capture_output=True, text=True)
        row = dict(command=list(map(str, command)), load=load, returncode=result.returncode,
                   stdout=result.stdout, stderr=result.stderr, **metadata)
        record['samples'].append(row)
        save()
        result.check_returncode()
        row['result'] = json.loads(result.stdout)
        save()
        return row['result']

    save()
    try:
        for block in range(2):
            arms = ['stage1', 'stage2'] if block == 0 else ['stage2', 'stage1']
            for b1, b2 in record['residual_bounds']:
                for name, n in RESIDUALS.items():
                    for base in record['bases']:
                        for arm in arms:
                            run(['pminus', n, base, b1, b1 if arm == 'stage1' else b2],
                                phase='residual', case=name, block=block, arm=arm)
            for case in corpus():
                if case['name'] not in ['secp256k1', 'P-384', 'Curve448', 'P-521']:
                    continue
                results = {}
                for arm in arms:
                    results[arm] = run(['construction-pminus', case['n'], str(arm == 'stage2').lower()],
                                       phase='construction', case=case['name'], block=block, arm=arm)
                if case['name'] == 'P-521':
                    assert results['stage1']['certificate'] == results['stage2']['certificate']
            print(f'completed block {block}', flush=True)
        record['completion'] = 'complete'
    except BaseException as error:
        record['completion'] = f'failed: {error}'
        raise
    finally:
        save()


if __name__ == '__main__':
    main()
