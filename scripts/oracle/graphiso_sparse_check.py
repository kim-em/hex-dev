#!/usr/bin/env python3
"""Differential checks of the verified sparse port against pinned sparse nauty.

Build ``hexgraphiso_sparse_probe`` first. Checks exact indirect-sort tie order,
arbitrary valid refinement inputs, and complete searches on the existing
fixture corpus plus deterministic random graphs. ``--trace-corpus`` also
replays every input in the extended dense trace corpus with sparse nauty.
"""
from __future__ import annotations

import argparse
import gzip
import json
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.oracle.graphiso_nauty import _build_shim, _shim_input, check_records
from scripts.oracle.common import _validate_fixture


def lean(cases, binary):
    proc = subprocess.run([str(binary)], input="".join(json.dumps(c) + "\n" for c in cases),
                          capture_output=True, text=True, check=True, timeout=600)
    result = [json.loads(line) for line in proc.stdout.splitlines()]
    if len(result) != len(cases):
        raise AssertionError(f"Lean returned {len(result)} answers for {len(cases)} inputs")
    return result


def compare(cases, actual, expected, name):
    for c, a, e in zip(cases, actual, expected, strict=True):
        if a != e:
            raise AssertionError(f"{name}:\ninput={json.dumps(c)}\nLean={a}\nC={e}")
    print(f"sparse {name}: {len(cases)} exact comparisons", flush=True)


def sorts(binary, shim, rng):
    cases = []
    for size in [0, 1, 2, 10, 11, 12, 63, 64, 65, 319, 320, 321, 640]:
        for keys in [1, 2, 3, 7, max(1, size)]:
            for padding in [0, 3]:
                n = size + 2 * padding
                x = list(range(n))
                rng.shuffle(x)
                y = [rng.randrange(keys) for _ in x]
                cases.append(dict(mode="sort", x=x, y=y, start=padding, len=size))
    payload = "".join(f"{len(c['x'])} {c['start']} {c['len']}\n" +
                      " ".join(map(str, c['x'])) + "\n" +
                      " ".join(map(str, c['y'])) + "\n" for c in cases) + "-1 0 0\n"
    proc = subprocess.run([str(shim), "--sort"], input=payload, capture_output=True,
                          text=True, check=True, timeout=60)
    expected = [list(map(int, line.split())) for line in proc.stdout.splitlines()]
    compare(cases, lean(cases, binary), expected, "sort")


def refinements(binary, shim, rng):
    cases = []
    for n in [1, 2, 4, 8, 16, 31, 63, 64, 65, 128, 321]:
        for t in range(20):
            level = 1 + t % 4
            edges = [[i, j] for i in range(n) for j in range(i+1, n)
                     if rng.random() < [0, 2/n, 0.15, 0.5, 1][t % 5]]
            lab = list(range(n))
            rng.shuffle(lab)
            ends = sorted(set([n-1] + [i for i in range(n-1) if rng.random() < 0.1]))
            # Force the shallow distance branch for several connected and
            # disconnected inputs, and an empty active set in others.
            if t % 4 == 0 and n >= 16:
                ends = [0, n-1]
                level = 1 + t % 2
                active = [0]
            else:
                active = [i for i in [0] + [e+1 for e in ends[:-1]]
                          if rng.random() < (0 if t % 7 == 0 else 0.7)]
            ptn = [rng.randrange(level+1) if i in ends else max(n+2, level+1) for i in range(n)]
            cases.append(dict(mode="refine", kind="graphisosparse", n=n, k=1,
                              colors=[0]*n, edges=edges, lab=lab, ptn=ptn, level=level,
                              numcells=len(ends), active=active))
    payload = "".join(_shim_input(c) + f"{c['level']} {c['numcells']}\n" +
                      " ".join(map(str, c['lab'])) + "\n" +
                      " ".join(map(str, c['ptn'])) + "\n" +
                      " ".join(str(int(i in c['active'])) for i in range(c['n'])) + "\n"
                      for c in cases) + "-1 -1\n"
    proc = subprocess.run([str(shim), "--refine"], input=payload, capture_output=True,
                          text=True, check=True, timeout=60)
    expected = [json.loads(line) for line in proc.stdout.splitlines()]
    for e in expected:
        e['active'] = [i for i, b in enumerate(e['active']) if b]
    compare(cases, lean(cases, binary), expected, "refinement")


def searches(binary, rng, trace_corpus, out):
    path = ROOT / "conformance-fixtures/HexGraphIso/graphiso.jsonl"
    cases = [json.loads(line) for line in path.read_text().splitlines()]
    if trace_corpus:
        with gzip.open(ROOT / "conformance-fixtures/HexGraphIso/trace.jsonl.gz", "rt") as f:
            cases.extend(dict(case=f"{c['corpus']}/{c['name']}", **c['input'])
                         for c in map(json.loads, f))
    for n in [6, 7, 8, 16, 31, 63, 64, 65, 128]:
        for t in range(25):
            k = 1 + t % min(5, n)
            colors = [i % k for i in range(n)]
            rng.shuffle(colors)
            edges = [[i, j] for i in range(n) for j in range(i+1, n)
                     if rng.random() < [0, 2/n, 0.15, 0.5, 1][t % 5]]
            cases.append(dict(case=f"random-{n}-{t}", n=n, k=k, colors=colors, edges=edges))
    cases.append(dict(case="large-order", n=30, k=1, colors=[0]*30, edges=[]))
    answers = lean(cases, binary)
    for answer in answers:
        _validate_fixture(answer)
    checked, autos = check_records(answers)
    print(f"sparse search: {checked} cases, {autos} exact group checks", flush=True)
    if out:
        out.write_text("".join(json.dumps(a, separators=(',', ':')) + "\n" for a in answers))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=ROOT / ".lake/build/bin/hexgraphiso_sparse_probe")
    parser.add_argument("--trace-corpus", action="store_true")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    shim = _build_shim()
    rng = random.Random(47)
    sorts(args.binary, shim, rng)
    refinements(args.binary, shim, rng)
    searches(args.binary, rng, args.trace_corpus, args.out)


if __name__ == "__main__":
    main()
