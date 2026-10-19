#!/usr/bin/env python3
"""Collect the frozen optional-factorization capability corpus, once per subject.

Uses the committed plan, one leased CPU and serial trials. Keeps every outcome.
Existing fixtures and reports are never overwritten. This is capability evidence,
not a performance comparison or a promise of arbitrary 60-digit support.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time
from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
SUPPORT = r'''
import HexIntFactor.Export
open Lean Elab Command Hex.Nat

private def fields (raw : PartialFactorization) : List (String × Json) :=
  [("residual", toJson (toString raw.residual)),
   ("factors", toJson (raw.factors.map fun e => (toString e.prime, e.exponent)))]

private meta def emit (fs : List (String × Json)) : MetaM Unit :=
  logInfo m!"FACTOR_MEASURE {(Json.mkObj fs).compress}"

meta def measureNative (n fuel : Nat) : MetaM Unit := do
  let start ← IO.monoNanosNow
  let found := Internal.factorCountedWith? ⟨2, 65536, .off⟩ 8 n
    (Hex.Rand.ofSeed 1729) fuel false .off
  let (status, attempts, data) := match found with
    | .ok s => ("complete", s.attempts, fields ⟨n, s.factorization.raw.factors, 1⟩)
    | .error f => (reprStr f.stop, f.attempts, (f.snapshot.map (fun (s : PartialSnapshot) => fields s.raw)).getD [])
  let finish ← IO.monoNanosNow
  emit ([("stage", toJson "native"), ("subject", toJson (toString n)),
    ("fuel", toJson fuel), ("status", toJson status), ("attempts", toJson attempts),
    ("ns", toJson (finish - start))] ++ data)

meta def measureExternal (n index attempts : Nat) (gp : String) : MetaM Unit := do
  let start ← IO.monoNanosNow
  let produced ← Pari.run n (executable := gp)
  let finish ← IO.monoNanosNow
  let .ok text := produced | do
    emit [("stage", toJson "process"), ("subject", toJson (toString n)),
      ("status", toJson (reprStr produced)), ("ns", toJson (finish - start))]
    return
  emit [("stage", toJson "process"), ("subject", toJson (toString n)),
    ("status", toJson "success"), ("ns", toJson (finish - start)),
    ("bytes", toJson text.utf8ByteSize), ("output", toJson text)]
  let start ← IO.monoNanosNow
  let parsed := Pari.parse {} n text
  let finish ← IO.monoNanosNow
  emit [("stage", toJson "parse"), ("subject", toJson (toString n)),
    ("status", toJson (if parsed.isOk then "success" else reprStr parsed)),
    ("ns", toJson (finish - start))]
  let .ok proposal := parsed | return
  let budget : ImportBudget := { completion := { ({} : ImportBudget).completion with maxAttempts := attempts } }
  let start ← IO.monoNanosNow
  let prepared := FactorImport.prepare budget n proposal (Hex.Rand.ofSeed 1729)
  let finish ← IO.monoNanosNow
  let .ok candidate := prepared | do
    emit [("stage", toJson "completion"), ("subject", toJson (toString n)),
      ("status", toJson (match prepared with | .error e => reprStr e | _ => "")),
      ("ns", toJson (finish - start))]
    return
  emit ([("stage", toJson "completion"), ("subject", toJson (toString n)),
    ("status", toJson (if candidate.raw.residual == 1 then "complete" else "partial")),
    ("ns", toJson (finish - start)), ("attempts", toJson candidate.attempts),
    ("unresolved", toJson (reprStr candidate.unresolved)),
    ("events", toJson (reprStr candidate.events))] ++ fields candidate.raw)
  let start ← IO.monoNanosNow
  let accepted := FactorImport.accept n candidate.raw
  let finish ← IO.monoNanosNow
  emit [("stage", toJson "compiled_check"), ("subject", toJson (toString n)),
    ("status", toJson (if accepted.isOk then "accepted" else "rejected")),
    ("ns", toJson (finish - start))]
  let .ok value := accepted | return
  let start ← IO.monoNanosNow
  try
    let name := Name.str `Hex.IntFactorFrozen s!"case{index}"
    let source ← FactorExport.source name n value
    let finish ← IO.monoNanosNow
    let path := s!"HexIntFactor/Frozen/Case{index}.lean"
    let handle ← IO.FS.Handle.mk path .writeNew
    handle.putStr source
    handle.flush
    emit [("stage", toJson "export"), ("subject", toJson (toString n)),
      ("status", toJson "written"), ("ns", toJson (finish - start)),
      ("bytes", toJson source.utf8ByteSize), ("module", toJson s!"HexIntFactor.Frozen.Case{index}")]
  catch e =>
    emit [("stage", toJson "export"), ("subject", toJson (toString n)),
      ("status", toJson (← e.toMessageData.toString)),
      ("ns", toJson ((← IO.monoNanosNow) - start))]
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--gp', required=True)
    parser.add_argument('--report', default='reports/hex-int-factor-external.json')
    args = parser.parse_args()
    plan_file = ROOT / 'reports/hex-int-factor-external-plan.json'
    plan = json.loads(plan_file.read_text())
    report_file = ROOT / args.report
    if report_file.exists():
        raise SystemExit(f'report already exists: {report_file}')
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    report = {'plan_sha256': hashlib.sha256(plan_file.read_bytes()).hexdigest(),
              'host': platform.node(), 'platform': platform.platform(), 'cpu': cpu,
              'load_start': list(os.getloadavg()), 'revision': subprocess.check_output(
                  ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'gp': str(Path(args.gp).resolve()), 'outcomes': []}
    # Reserve the report exclusively before starting work, then retain each completed sample.
    with report_file.open('x') as f:
        json.dump(report, f, indent=2)
    def save():
        report_file.write_text(json.dumps(report, indent=2) + '\n')
    with tempfile.TemporaryDirectory(prefix='MeasureExternal', dir=ROOT / 'HexIntFactor') as temp:
        scratch = Path(temp)
        prefix = 'HexIntFactor.' + scratch.name
        (scratch / 'Support.lean').write_text(SUPPORT)
        def run(module, text, kind):
            (scratch / f'{module}.lean').write_text(text)
            start = time.monotonic_ns()
            result = subprocess.run(['lake', 'build', f'+{prefix}.{module}:olean'],
                                    cwd=ROOT, text=True, capture_output=True, timeout=600)
            output = result.stdout + result.stderr
            rows = [json.loads(line.split('FACTOR_MEASURE ', 1)[1]) for line in output.splitlines()
                    if 'FACTOR_MEASURE ' in line]
            report['outcomes'].extend(rows)
            report['outcomes'].append({'stage': kind, 'module': prefix + '.' + module,
                                       'returncode': result.returncode,
                                       'ns': time.monotonic_ns() - start, 'log': output})
            save()
            print(f'{module}: {result.returncode}', flush=True)
            if result.returncode:
                raise RuntimeError(output)
        try:
            # Build the support before measurements to keep compilation out of stage timings.
            run('Prepare', f'import {prefix}.Support\n', 'preparation')
            subjects = plan['subjects'] + [plan['exhaustion_control']['subject']]
            for index, subject in enumerate(subjects):
                for fuel in plan['native']['factorFuel']:
                    run(f'Native{index}Fuel{fuel}', f'import {prefix}.Support\n'
                        f'run_cmd Lean.Elab.Command.liftTermElabM <| measureNative {subject} {fuel}\n', 'native_module')
                attempts = plan['completion']['maxAttempts'] if index < len(plan['subjects']) else 0
                gp = json.dumps(str(Path(args.gp).resolve()))
                run(f'External{index}', f'import {prefix}.Support\n'
                    f'run_cmd Lean.Elab.Command.liftTermElabM <| measureExternal {subject} {index} {attempts} {gp}\n', 'external_module')
                fixture = ROOT / f'HexIntFactor/Frozen/Case{index}.lean'
                if fixture.exists():
                    start = time.monotonic_ns()
                    replay = subprocess.run(['lake', 'build', f'+HexIntFactor.Frozen.Case{index}:olean'],
                                            cwd=ROOT, text=True, capture_output=True, timeout=180,
                                            env=dict(os.environ, HEX_INT_FACTOR_GP='/no-gp-during-replay'))
                    report['outcomes'].append({'stage': 'fresh_module_replay', 'subject': subject,
                        'returncode': replay.returncode, 'ns': time.monotonic_ns() - start,
                        'source_bytes': fixture.stat().st_size, 'log': replay.stdout + replay.stderr})
                    save()
                    if replay.returncode:
                        print(replay.stdout + replay.stderr, flush=True)
        finally:
            report['load_finish'] = list(os.getloadavg())
            save()
            for base in (ROOT / '.lake/build/lib/lean', ROOT / '.lake/build/ir'):
                shutil.rmtree(base / 'HexIntFactor' / scratch.name, ignore_errors=True)
    lease.close()


if __name__ == '__main__':
    main()
