#!/usr/bin/env python3
"""Observe caller resources of plain primality? without changing Lean accounting."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick

MODULE = 'HexPrimality.ProofProbe.Curve25519.FallbackOptions'
SOURCE = ROOT/'bench'/Path(MODULE.replace('.', '/')+'.lean')
CASES = [('secp256k1', 2**256-2**32-977, '2 ^ 256 - 2 ^ 32 - 977'),
         ('P-384', 2**384-2**128-2**96+2**32-1, '2 ^ 384 - 2 ^ 128 - 2 ^ 96 + 2 ^ 32 - 1'),
         ('Curve448', 2**448-2**224-1, '2 ^ 448 - 2 ^ 224 - 1')]
HEADER = '''module
public import HexIntFactor
public import Lean
public section
open Lean Elab Tactic
elab "measure_primality" : tactic => do
  let hb ← IO.getNumHeartbeats
  try
    evalTactic (← `(tactic| primality?))
  finally
    let used ← IO.getNumHeartbeats
    IO.println s!"HEARTBEATS_RAW {used - hb}"
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if args.output.exists() or SOURCE.exists(): parser.error('use fresh output and module paths')
    subprocess.run(['lake','build','HexIntFactor'],cwd=ROOT,check=True)
    cpu=pick()
    paths=['HexPrimality/Construction.lean','HexPrimality/Elab.lean',
           'HexIntFactor/Construction.lean','HexIntFactor/Primality.lean','lakefile.lean',
           'scripts/bench/primality_fallback_options.py']
    record=dict(cpu=cpu,host=platform.node(),toolchain=(ROOT/'lean-toolchain').read_text(),
                commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
                sources={p:(ROOT/p).read_text() for p in paths},
                source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths},
                heartbeat_unit='raw IO.getNumHeartbeats delta; divide by 1000 for user heartbeats',
                samples=[],completion='running')
    def save(): args.output.write_text(json.dumps(record,indent=2)+'\n')
    try:
        for name,n,power in CASES:
            for form,goal in [('numeral',str(n)),('power',power)]:
                for allowance in [None,4000000]:
                    opts='' if allowance is None else f'set_option maxHeartbeats {allowance}\n'
                    source=HEADER+opts+f'example : Hex.Nat.Prime ({goal}) := by measure_primality\n'
                    SOURCE.write_text(source)
                    artifact=ROOT/'.lake/build/lib/lean'/Path(MODULE.replace('.','/')+'.olean')
                    artifact.unlink(missing_ok=True)
                    command=['taskset','-c',str(cpu),'lake','build',MODULE]
                    row=dict(case=name,form=form,maxHeartbeats=allowance,source=source,
                             command=command,load_before=os.getloadavg())
                    start=time.monotonic_ns()
                    p=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,
                                     env=dict(os.environ,LEAN_NUM_THREADS='1'))
                    row.update(stdout=p.stdout,stderr=p.stderr,returncode=p.returncode,
                               elapsed_ns=time.monotonic_ns()-start,load_after=os.getloadavg())
                    observed = re.search(
                        r'^(?:info: [^\n]+\.lean:\d+:\d+: )?HEARTBEATS_RAW ([0-9]+)$',
                        p.stdout, re.MULTILINE)
                    if observed:
                        row['heartbeats_raw'] = int(observed.group(1))
                    record['samples'].append(row)
                    save()
                    print(name,form,allowance,p.returncode,flush=True)
                    if observed is None:
                        raise RuntimeError('resource harness failed before observation; sample retained')
                    if allowance is None and p.returncode and 'maximum number of heartbeats' not in p.stdout:
                        raise RuntimeError('unexpected default-options failure; sample retained')
                    if allowance is not None and p.returncode:
                        raise RuntimeError('finite caller allowance failed; sample retained')
        record['completion']='complete'
    except BaseException as exc:
        record['completion']=str(exc)
        raise
    finally:
        SOURCE.unlink(missing_ok=True)
        save()

if __name__=='__main__': main()
