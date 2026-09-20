#!/usr/bin/env python3
"""Attribute supplied Hex certificate replay with fresh kernel checkers.

Components overlap (arithmetic includes witnesses); do not add their timings.
The complete proof expands all local definitions and opaque theorems.
"""
from __future__ import annotations
import argparse
import copy
import math
import json
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import run
from scripts.bench.primality_kernel_direct import SUFFIX


def parse_certificate(literal):
    tokens = re.findall(r"Hex\.Nat\.PrimeCert\.(?:pock3Sieve|pock3|pock|small)|[0-9]+|[()\[\],]", literal)
    i = 0
    def take(expected=None):
        nonlocal i
        token = tokens[i]
        i += 1
        if expected is not None and token != expected:
            raise ValueError((token, expected))
        return token
    def node():
        kind = take().split(".")[-1]
        n = int(take())
        extra = [int(take()) for _ in range({"small": 0, "pock": 0, "pock3": 3, "pock3Sieve": 4}[kind])]
        fs = []
        if kind != "small":
            take("[")
            while tokens[i] != "]":
                take("(")
                a = int(take()); take(",")
                e = int(take()); take(",")
                child = node(); take(")")
                fs.append((a, e, child))
                if tokens[i] != ",": break
                take(",")
            take("]")
        return dict(kind=kind, n=n, extra=extra, fs=fs)
    result = node()
    if i != len(tokens): raise ValueError("trailing tokens")
    return result


def render(c):
    head = "Hex.Nat.PrimeCert." + c["kind"] + " " + " ".join(map(str, [c["n"], *c["extra"]]))
    return head if c["kind"] == "small" else head + " " + factors(c)


def factors(c):
    return "[" + ", ".join(f"({a}, {e}, {render(child)})" for a, e, child in c["fs"]) + "]"


def components(c):
    terms = {k: [] for k in ["leaves", "subjects", "product", "witnesses", "arithmetic", "powers"]}
    counts = dict(nodes=0, leaves=0, entries=0, powers=0, repeated_bases=0, divisor_tests=0)
    subjects = []
    def visit(c):
        n, kind = c["n"], c["kind"]
        subjects.append(n)
        if kind == "small":
            counts["leaves"] += 1
            terms["leaves"].append(f"Hex.Nat.isTablePrime {n}")
            return
        counts["nodes"] += 1
        fs = factors(c)
        terms["subjects"].append(f"Hex.Nat.subjectsOk {fs}")
        terms["product"].append(f"(Hex.Nat.pockProduct {n-1} {fs}).beq " + str(math.prod(child['n'] ** (e+1) for _,e,child in c['fs'])))
        terms["witnesses"].append(f"Hex.Nat.checkWitnesses {n} {fs}")
        fn = {"pock": "checkPockArith", "pock3": "checkPock3Arith", "pock3Sieve": "checkPock3SieveArith"}[kind]
        terms["arithmetic"].append(f"Hex.Nat.{fn} " + " ".join(map(str,[n,*c['extra']])) + " " + fs)
        if kind == "pock3Sieve": counts["divisor_tests"] += c["extra"][-1] - 1
        prev = None
        for a, e, child in c["fs"]:
            counts["entries"] += 1
            exponents = [(n-1)//child['n']]
            if a != prev: exponents.append(n-1)
            else: counts["repeated_bases"] += 1
            for exponent in exponents:
                counts["powers"] += 1
                terms["powers"].append(f"(HexArith.powModNat {a} {exponent} {n}).beq {pow(a,exponent,n)}")
            prev = a
            visit(child)
    visit(c)
    counts["repeated_subjects"] = len(subjects) - len(set(subjects))
    return {k: " && ".join(f"({t})" for t in ts) or "true" for k, ts in terms.items()}, counts

def match_bases(node):
    if not node['fs']: return
    n = node['n']
    # Same bounded candidate list as primality_primecert_sources.py.
    candidates = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
                  43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    a = next(a for a in candidates if pow(a,n-1,n) == 1 and all(
        math.gcd(pow(a,(n-1)//child['n'],n)-1,n) == 1 for _,_,child in node['fs']))
    node['fs'] = [(a,e,child) for _,e,child in node['fs']]
    for _,_,child in node['fs']: match_bases(child)


TIMER = SUFFIX[:SUFFIX.index("run_cmd do")] + r'''
run_cmd do
  let original ← Lean.getEnv
  let ready ← IO.mkRef original.toKernelEnv
  let ready ← ready.get
  let env := Lean.Environment.ofKernelEnv ready
  let groups := GROUPS
  for block in [0:4] do
    for group in groups do
      for name in (if block % 2 == 0 then group else group.reverse) do
        let some (.thmInfo info) := original.find? name | throwError "missing theorem"
        let value := inlineLocal original info.value
        let type := inlineLocal original info.type
        unless (value.getUsedConstants ++ type.getUsedConstants).all original.isImportedConst do
          throwError "local dependency escaped expansion"
        let proof := Lean.mkApp (Lean.mkLambda `h .default type (Lean.mkBVar 0)) value
        let input ← IO.mkRef (env, proof)
        let (env, proof) ← input.get
        let start ← IO.monoNanosNow
        let checked ← IO.mkRef (Lean.Kernel.check env {} proof)
        let checked ← checked.get
        let stop ← IO.monoNanosNow
        match checked with
        | .error _ => throwError "kernel rejected component"
        | .ok _ => pure ()
        Lean.logInfo m!"COMPONENT {block} {name} {stop - start}"
'''


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('record', type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--compare-bases', action='store_true',
                   help='pair each original complete Boolean check with a common-base check')
    p.add_argument('--prepare-matched', action='store_true',
                   help='write a source record with one valid common base per node; no timing')
    args = p.parse_args()
    module = 'HexPrimality.ProofProbe.Curve25519.Attribution'
    path = ROOT / 'bench' / (module.replace('.', '/')+'.lean')
    if path.exists() or args.output.exists(): p.error('use fresh probe/output paths')
    data = json.loads(args.record.read_text())
    source = 'module\npublic import HexPrimality.Cert\npublic import Lean\npublic meta import Lean\npublic section\nset_option maxRecDepth 100000\n'
    groups, counts = [], {}
    matched = dict(cases=data['cases'], rows=[], preparation='Untrusted source generation; every proof must be validated by the kernel benchmark')
    for case in data['cases']:
        row = next(r for r in data['rows'] if r['case'] == case['name'] and r['system'] == 'hex' and r['status'] in ('ok', 'prepared'))
        literal = row['source'].split('def certificate : Hex.Nat.PrimeCert :=', 1)[1].split('\ntheorem', 1)[0]
        c = parse_certificate(literal)
        if args.prepare_matched:
            match_bases(c)
            body = '/- Offline matched certificate; Lean must check this untrusted output. -/\n\nmodule\npublic import HexPrimality.Cert\npublic import Lean\npublic meta import Lean\npublic section\nset_option maxRecDepth 100000\n'
            body += f'def certificate : Hex.Nat.PrimeCert := {render(c)}\n'
            body += f'theorem result : Hex.Nat.Prime {c["n"]} := Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)\n'
            matched['rows'].append(dict(case=case['name'], system='hex', status='prepared', source=body))
        terms, counts[case['name']] = components(c)
        full = dict(full=f'Hex.Nat.checkPrime ({render(c)})')
        if args.compare_bases:
            matched_c = copy.deepcopy(c)
            match_bases(matched_c)
            full['common'] = f'Hex.Nat.checkPrime ({render(matched_c)})'
        terms = dict(**full, **terms)
        names = []
        for part, term in terms.items():
            name = case['name'].replace('-','_') + '_' + part
            source += f'theorem {name} : ({term}) = true := by decide +kernel\n'
            names.append('`'+name)
        groups.append('['+', '.join(names)+']')
    if args.prepare_matched:
        matched['counts'] = counts
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(matched,indent=2)+'\n')
        return
    source += TIMER.replace('GROUPS', '['+', '.join(groups)+']')
    cpu = pick()
    path.write_text(source)
    artifact = ROOT / '.lake/build/lib/lean' / (module.replace('.', '/')+'.olean')
    artifact.unlink(missing_ok=True)
    try:
        result = run(['lake','build','+'+module+':olean'], ROOT, 180, cpu)
        record = dict(schema='primality-replay-attribution/1', host=platform.node(), cpu=cpu,
            commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
            toolchain=(ROOT/'lean-toolchain').read_text().strip(),
            diff=subprocess.check_output(['git','diff','HEAD'],text=True),
            source=source, counts=counts, result=result,
            rows=[dict(block=int(b), component=n, nanoseconds=int(t)) for b,n,t in re.findall(r'COMPONENT (\d+) (\S+) (\d+)',result['stdout'])])
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(record,indent=2)+'\n')
        print(result['stdout'])
        if result['status'] != 'ok': raise RuntimeError(result['stderr'])
    finally:
        path.unlink(missing_ok=True)

if __name__ == '__main__': main()
