#!/usr/bin/env python3
"""Kernel-replay the exact certificates retained by primality_adoption.py."""
from __future__ import annotations

import hashlib
import sys
import time
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
REPORT = ROOT / 'reports/primality/adoption/measurements.json'
SOURCE = ROOT / 'bench/HexPrimalityTheory/ProofProbe/Adoption.lean'
MANIFEST = REPORT.with_name('kernel-replay.json')
sys.path.insert(0, str(ROOT / 'scripts/ci'))
from check_ecpp_pari import scratch_modules


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def check_dispatch(data):
    """Confirm current-route exhaustion in an importing Lean elaborator module."""
    cases = {case['id']: case for case in data['cases']}
    selected = []
    for bits, limit in [(256, 1), (512, 2)]:
        eligible = [row for row in data['samples']
                    if row['case'] in cases and row['bits'] == bits
                    and cases[row['case']]['native_verdict'] == 'success'
                    and row.get('result', {}).get('status', '').endswith('exhausted')]
        assert len(eligible) >= limit
        selected.extend(eligible[:limit])
    source = """import HexIntFactor.Primality

open Lean

set_option maxHeartbeats 0

run_cmd Lean.Elab.Command.liftTermElabM do
"""
    for row in selected:
        n = row['subject']
        attempts = row['result']['attempts']
        source += f"""  let (result, allocations) ← Hex.PrimalityTactic.construct {n} Hex.Nat.constructionBudget
  unless allocations == [(``Hex.Nat.interleavedConstructionFactor, 1024)] do
    throwError "unexpected construction allocation"
  match result with
  | .ok _ => throwError "expected construction exhaustion for {n}"
  | .error f =>
    unless f.stop == .exhausted && f.attempts == {attempts} &&\n        f.rand.state == {row['result']['rand_state']} do
      throwError "construction outcome changed for {n}"
    logInfo m!"CURRENT_CONSTRUCTION {row['case']}: exhausted after {{f.attempts}} attempts"
"""
    with scratch_modules() as folder:
        (folder / 'Dispatch.lean').write_text(source)
        module = 'HexECPPTheory.' + folder.name + '.Dispatch'
        command = ['lake', 'build', '+' + module + ':olean']
        start = time.monotonic_ns()
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        log = run.stdout + run.stderr
    REPORT.with_name('dispatch.log').write_text(log)
    confirmations = [line for line in log.splitlines() if 'CURRENT_CONSTRUCTION ' in line]
    record = dict(policy='interleaved', source=source, cases=[r['case'] for r in selected],
                  command=command, wall_ns=time.monotonic_ns() - start,
                  returncode=run.returncode, confirmations=confirmations, log_sha256=digest(log))
    REPORT.with_name('dispatch.json').write_text(json.dumps(record, indent=2) + '\n')
    if run.returncode or len(confirmations) != len(selected):
        raise RuntimeError(log)
    print('Confirmed importing-module exhaustion on', len(selected), 'current-route ECPP comparisons')


def main():
    if MANIFEST.exists() or SOURCE.exists():
        raise RuntimeError('replay outputs already exist; preserve completed evidence')
    data = json.loads(REPORT.read_text())
    assert data['complete']
    source = '''/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityTheory.Prime

public section

/-! Frozen certificates from the adopted factor-search comparison. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

'''
    certificates = {}
    links = []
    for index, row in enumerate(data['samples']):
        result = row.get('result', {})
        if result.get('status') != 'success':
            continue
        certificate = result['certificate']
        sha = digest(certificate)
        if sha not in certificates:
            theorem = 'Hex.PrimalityAdoption.h' + sha[:20]
            subject = row['subject']
            source += f'''/-- Frozen certificate for {subject}. -/
theorem {theorem} : _root_.Nat.Prime {subject} :=
  Hex.Nat.natPrime_of_checkPrimeAt (c := {certificate}) (by decide +kernel)

/-- info: '{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms {theorem}

'''
            certificates[sha] = dict(subject=subject, theorem=theorem, certificate=certificate)
        links.append(dict(sample=index, certificate_sha256=sha))
    source = source.rstrip() + "\n"
    SOURCE.write_text(source)
    command = ['lake', 'build', 'HexPrimalityTheory.ProofProbe.Adoption']
    run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    log = run.stdout + run.stderr
    REPORT.with_name('kernel-replay.log').write_text(log)
    manifest = dict(measurements_sha256=digest(REPORT.read_text()),
                    source=str(SOURCE.relative_to(ROOT)), source_sha256=digest(source),
                    certificates=certificates, links=links, build_command=command,
                    build_returncode=run.returncode, log_sha256=digest(log))
    MANIFEST.write_text(json.dumps(manifest, indent=2) + '\n')
    if run.returncode:
        raise RuntimeError(log)
    print('Kernel-replayed', len(certificates), 'certificates with guarded axiom audits', flush=True)
    check_dispatch(data)


if __name__ == '__main__':
    main()
