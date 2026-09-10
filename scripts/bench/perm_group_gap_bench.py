#!/usr/bin/env python3
"""Measure comparable HexPermGroup operations in one persistent GAP process.

The process prepares its query groups once.  The ``construct`` request instead
creates a fresh group and deterministic stabilizer chain for every repeat, so
cached order queries are never compared with Hex construction.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


SERVICE = r'''
input := InputTextUser();;
s := PermList([2,1,3,4]);;
c := PermList([2,3,4,1]);;
r := PermList([1,4,3,2]);;
G := Group([s,c]);;
D := Group([c,r]);;
StabChain(G);; StabChain(D);;
while true do
  line := Chomp(ReadLine(input));
  if line = "quit" then break; fi;
  fields := SplitString(line, " ");;
  op := fields[1];; count := Int(fields[2]);;
  start := Runtime();; checksum := 0;;
  if op = "ping" then checksum := 1;
  elif op = "construct" then
    for i in [1..count] do H := Group([s,c,s,()]);; StabChain(H);; checksum := checksum + Size(H);; od;
  elif op = "membership" then
    # GAP acts on the right: c*s represents Hex s.comp c.
    for i in [1..count] do if c*s in G then checksum := checksum + 1; fi; od;
  elif op = "order" then
    for i in [1..count] do checksum := checksum + Size(G);; od;
  elif op = "stabilizer" then
    for i in [1..count] do checksum := checksum + Size(Stabilizer(G,1));; od;
  elif op = "intersection" then
    for i in [1..count] do checksum := checksum + Size(Intersection(G,D));; od;
  elif op = "blocks" then
    for i in [1..count] do checksum := checksum + Length(Blocks(D,[1..4],[1,3]));; od;
  elif op = "normal" then
    T := Group([s]);;
    for i in [1..count] do checksum := checksum + Size(NormalClosure(G,T)) + Size(DerivedSubgroup(G));; od;
  elif op = "products" then
    C2 := Group([(1,2)]);;
    for i in [1..count] do checksum := checksum + Size(DirectProduct(C2,C2)) + Size(WreathProductImprimitiveAction(C2,C2));; od;
  else Error("unknown operation: ", op); fi;
  Print("HEXGAP ", op, " ", Runtime()-start, " ", checksum, "\n");
od;
QUIT_GAP(0);
'''


CASES = (
    ("construct", 200),
    ("membership", 20_000),
    ("order", 20_000),
    ("stabilizer", 2_000),
    ("intersection", 1_000),
    ("blocks", 1_000),
    ("normal", 500),
    ("products", 200),
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    gap = os.environ.get("GAP") or shutil.which("gap")
    if not gap:
        raise SystemExit("HexPermGroup GAP benchmark requires GAP")

    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as source:
        source.write(SERVICE)
        service_path = Path(source.name)
    try:
        process = subprocess.Popen(
            [gap, "-q", "--quitonbreak", str(service_path)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert process.stdin is not None and process.stdout is not None
        process.stdin.write("ping 1\n")
        process.stdin.flush()
        while True:
            ready = process.stdout.readline()
            if not ready:
                raise RuntimeError("GAP stopped during persistent-process warmup")
            if ready.startswith("HEXGAP ping "):
                break
        rows = []
        for operation, repeats in CASES:
            before = time.monotonic_ns()
            process.stdin.write(f"{operation} {repeats}\n")
            process.stdin.flush()
            while True:
                line = process.stdout.readline()
                if not line:
                    raise RuntimeError(f"GAP stopped before replying to {operation}")
                if line.startswith("HEXGAP "):
                    break
            elapsed = time.monotonic_ns() - before
            _, returned, gap_ms, checksum = line.split()
            if returned != operation:
                raise RuntimeError(f"GAP replied for {returned}, expected {operation}")
            rows.append({
                "operation": operation,
                "repeats": repeats,
                "gap_runtime_ms": int(gap_ms),
                "round_trip_ns": elapsed,
                "per_call_ns": elapsed // repeats,
                "checksum": int(checksum),
            })
        process.stdin.write("quit\n")
        process.stdin.flush()
        if process.wait(timeout=10) != 0:
            raise RuntimeError("GAP benchmark service failed")
    finally:
        service_path.unlink(missing_ok=True)

    report = {
        "tool": "GAP",
        "protocol": "one persistent GAP process; line requests; process startup excluded",
        "methods": {
            "construction": "Group followed by StabChain with GAP defaults",
            "prepared_queries": "cached Group and StabChain; Size, reversed-product membership, Stabilizer",
            "subgroups": "Intersection, Blocks, NormalClosure, DerivedSubgroup; GAP attributes may cache after the first prepared query",
            "products": "DirectProduct and WreathProductImprimitiveAction",
        },
        "options": ["-q", "--quitonbreak"],
        "cases": rows,
    }
    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
    print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
