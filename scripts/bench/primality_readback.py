#!/usr/bin/env python3
"""Adjacent compiled readback measurements, forcing results before the clock."""
import argparse
import json
from pathlib import Path
import platform
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import run

SOURCE = '''module
public import HexPrimality.Sieve
public meta import HexPrimality.Sieve
public import Lean
public section
namespace Hex.PrimalityReadbackProbe
def oldScan (state : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | t, fuel + 1 =>
      if state.testBit t then Hex.Nat.numOfIndex t :: oldScan state (t+1) fuel
      else oldScan state (t+1) fuel

@[noinline] def measure (old : Bool) (bound state : Nat) : IO Lean.Json := do
  let input ← IO.mkRef (bound, state)
  let (bound, state) ← input.get
  let start ← IO.monoNanosNow
  let output ← IO.mkRef (if old then oldScan state 1 (Hex.Nat.indexWidth bound - 1)
    else Hex.Nat.bitsToList state bound)
  let output ← output.get
  let stop ← IO.monoNanosNow
  return Lean.Json.mkObj [("old", Lean.toJson old), ("nanos", Lean.toJson (stop-start)),
    ("count", Lean.toJson output.length), ("last", Lean.toJson output.getLast?)]

#eval show IO Unit from do
  let bound ← IO.mkRef (524289 : Nat)
  let bound ← bound.get
  let state ← IO.mkRef (Hex.Nat.sieve bound (bound.sqrt + 1))
  let state ← state.get
  for block in [0:2] do
    for old in (if block == 0 then [true, false] else [false, true]) do
      let row ← measure old bound state
      IO.println row.compress
end Hex.PrimalityReadbackProbe
'''

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    cpu = pick()
    module = 'HexPrimality.ProofProbe.Curve25519.Readback'
    source = ROOT/'bench'/Path(module.replace('.', '/')+'.lean')
    output = args.output
    if source.exists() or output.exists():
        raise RuntimeError('refusing to overwrite a probe or retained record')
    source.write_text(SOURCE)
    try:
        row = run(['lake', 'build', '+'+module+':olean'], ROOT, 60, cpu)
        row.update(cpu=cpu, host=platform.node(), source=SOURCE,
                   protocol='adjacent old/new arms, AB/BA; every completed sample retained')
        output.write_text(json.dumps(row, indent=2)+'\n')
        print(row['stdout']); print(row['stderr'])
        if row['status'] != 'ok':
            raise RuntimeError(row['status'])
    finally:
        source.unlink(missing_ok=True)

if __name__ == '__main__':
    main()
