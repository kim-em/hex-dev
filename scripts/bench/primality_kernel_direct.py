#!/usr/bin/env python3
"""Time warm kernel rechecks of complete supplied proof bodies after elaboration.

Local auxiliary theorems and definitions are recursively expanded and pending
asynchronous checks are drained before the timer. Each call creates a fresh
checker. Imported library theorems remain dependencies in both systems.
"""
from __future__ import annotations

import argparse
import hashlib
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

SUFFIX = r'''
meta partial def inlineLocal (env : Lean.Environment) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub => match sub with
    | .const n levels =>
      if env.isImportedConst n then none else
        match env.find? n with
        | some info => (info.value? (allowOpaque := true)).map fun value =>
            inlineLocal env (value.instantiateLevelParams info.levelParams levels)
        | none => none
    | _ => none

run_cmd do
  let env ← Lean.getEnv
  let some (.thmInfo info) := env.find? `RESULT_NAME
    | throwError "missing result theorem"
  let value := inlineLocal env info.value
  let type := inlineLocal env info.type
  unless (value.getUsedConstants ++ type.getUsedConstants).all env.isImportedConst do
    throwError "unexpanded local proof dependency"
  -- The identity application checks the proof against its declared goal type.
  let proof := Lean.mkApp (Lean.mkLambda `h .default type (Lean.mkBVar 0)) value
  -- Explicitly finish pending elaboration-time kernel tasks before timing.
  let ready ← IO.mkRef env.toKernelEnv
  let ready ← ready.get
  let env := Lean.Environment.ofKernelEnv ready
  -- An invalid equality must be rejected by this same kernel entry point.
  let badType := Lean.mkApp3 (Lean.mkConst ``Eq [.succ .zero])
    (Lean.mkConst ``Bool) (Lean.mkConst ``Bool.true) (Lean.mkConst ``Bool.false)
  let badProof := Lean.mkApp (Lean.mkLambda `h .default badType (Lean.mkBVar 0))
    Lean.reflBoolTrue
  match Lean.Kernel.check env {} badProof with
  | .error _ => pure ()
  | .ok _ => throwError "kernel accepted the negative control"
  let corrupt := value.replace fun e => match e with
    | .lit (.natVal n) => if n == SUBJECT then some (Lean.mkRawNatLit (n + 2)) else none
    | _ => none
  if corrupt == value then throwError "subject corruption did not change the proof"
  let corrupt := Lean.mkApp (Lean.mkLambda `h .default type (Lean.mkBVar 0)) corrupt
  match Lean.Kernel.check env {} corrupt with
  | .error _ => pure ()
  | .ok _ => throwError "kernel accepted the corrupted proof"
  -- Change only a Hex witness base: subjects, products, and ordering remain
  -- intact, so this control must reach the witness arithmetic.
  let corruptWitness := value.replace fun e => Id.run do
    unless e.isAppOfArity `Hex.Nat.PrimeCert.pock 2 ||
        e.isAppOfArity `Hex.Nat.PrimeCert.pock3 5 do return none
    let args := e.getAppArgs
    let fs := args.back!
    unless fs.isAppOfArity ``List.cons 3 do return none
    let fsArgs := fs.getAppArgs
    let entry := fsArgs[1]!
    unless entry.isAppOfArity ``Prod.mk 4 do return none
    let entryArgs := entry.getAppArgs
    let entry := Lean.mkAppN entry.getAppFn (entryArgs.set! 2 (Lean.mkRawNatLit 0))
    let fs := Lean.mkAppN fs.getAppFn (fsArgs.set! 1 entry)
    return some (Lean.mkAppN e.getAppFn (args.set! (args.size - 1) fs))
  let needsWitness := value.getUsedConstants.any fun name =>
    name == `Hex.Nat.PrimeCert.pock || name == `Hex.Nat.PrimeCert.pock3
  if needsWitness && corruptWitness == value then
    throwError "witness corruption did not change the proof"
  if corruptWitness != value then
    let bad := Lean.mkApp (Lean.mkLambda `h .default type (Lean.mkBVar 0)) corruptWitness
    match Lean.Kernel.check env {} bad with
    | .error _ => pure ()
    | .ok _ => throwError "kernel accepted the zero witness base"
    Lean.logInfo "DIRECT_WITNESS_CONTROL rejected"
  let input ← IO.mkRef (env, proof)
  let (env, proof) ← input.get
  let start ← IO.monoNanosNow
  let checked ← IO.mkRef (Lean.Kernel.check env {} proof)
  let checked ← checked.get
  let stop ← IO.monoNanosNow
  match checked with
  | .error _ => throwError "kernel recheck failed"
  | .ok _ => pure ()
  Lean.logInfo m!"DIRECT_KERNEL_NS {stop - start}"
  Lean.logInfo m!"DIRECT_DEPENDENCIES {value.getUsedConstants}"
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source_record', type=Path)
    parser.add_argument('--primecert-checkout', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--blocks', type=int, default=2)
    parser.add_argument('--hex-supplied', action='append', default=[], metavar='CASE=PATH',
                        help='check a supplied Hex proof instead of the construction corpus source')
    parser.add_argument('--primecert-supplied', action='append', default=[], metavar='CASE=PATH',
                        help='check an alternative supplied PrimeCert proof')
    parser.add_argument('--powers', action='store_true',
                        help='isolate modular powering and calibrate the two kernel versions')
    parser.add_argument('--upstream-power', action='store_true',
                        help='include the kernel definition from lean4#13490 in the power comparison')
    args = parser.parse_args()
    if args.output.exists() or args.blocks < 2 or args.blocks % 2:
        parser.error('use a new output path and an even block count >= 2')
    if args.upstream_power and not args.powers:
        parser.error('--upstream-power requires --powers')
    previous = json.loads(args.source_record.read_text())
    pc = args.primecert_checkout.resolve()
    cpu = pick()
    locations = {
        'hex': (ROOT, 'HexPrimality.ProofProbe.Curve25519.DirectKernel',
                ROOT/'bench/HexPrimality/ProofProbe/Curve25519/DirectKernel.lean'),
        'primecert': (pc, 'PrimeCert.Comparator.DirectKernel',
                      pc/'PrimeCert/Comparator/DirectKernel.lean')}
    record = dict(schema='hex-primality-direct-kernel/1', host=platform.node(),
                  cpu=cpu, blocks=args.blocks, source_record=str(args.source_record),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  protocol='trial-major adjacent Hex/PrimeCert; reverse systems in odd blocks; '
                           'one fresh kernel checker per call; all completed samples retained',
                  timing='Warm Kernel.check of the complete local proof body against its goal; '
                         'pending asynchronous checks explicitly drained before timing; '
                         'excludes imports, proof elaboration, expansion, and negative controls; '
                         'includes kernel reduction and type checking; imported library proofs '
                         'remain dependencies; separate pinned toolchains',
                  versions={}, cases=[c for c in previous['cases'] if 'primecert' in c], rows=[])
    supplied = {'hex': {}, 'primecert': {}}
    for system, entries in [('hex', args.hex_supplied), ('primecert', args.primecert_supplied)]:
        for entry in entries:
            name, separator, path = entry.partition('=')
            if not separator or name not in {c['name'] for c in record['cases']} or name in supplied[system]:
                parser.error('supplied proofs require a distinct corpus CASE=PATH for each system')
            source = Path(path).read_text()
            if not source.startswith('/-') or '\nmodule\n' not in source:
                parser.error('a supplied proof must have a header and use the module system')
            # Fixtures import their checker; probes additionally need Lean's
            # metaprogramming API for the direct kernel timer.
            probe = source.replace('\nmodule\n', '\nmodule\npublic import Lean\npublic meta import Lean\n', 1)
            supplied[system][name] = probe
            record.setdefault(f'supplied_{system}_sources', {})[name] = dict(
                path=path, source=source, sha256=hashlib.sha256(source.encode()).hexdigest(),
                origin='supplied certificate; does not establish construction success')
    if (args.hex_supplied or args.primecert_supplied) and args.powers:
        parser.error('supplied proofs are for complete certificates, not isolated powers')
    if args.powers:
        from scripts.bench.primality_kernel_diagnostic import RAW
        n = str(2**255 - 19)
        exponent = str(2**255 - 20)
        record['cases'] = [dict(name=name, n=n) for name in ['power-current', 'power-bits', 'power-div']]
        record['power_sources'] = {}
        for name, function in [('power-current', 'HexArith.powModNat'),
                               ('power-bits', 'powBits'), ('power-div', 'powDiv')]:
            body = 'module\npublic import HexPrimality.Cert\npublic import Lean\npublic meta import Lean\npublic section\n'
            body += RAW + f'\ntheorem result : {function} 2 {exponent} {n} = 1 := by decide +kernel\n'
            record['power_sources'][name] = {'hex': body}
        # The identical raw-div definition under the comparator's pinned kernel.
        raw_div = RAW[RAW.index('@[expose] noncomputable def powDiv'):]
        record['power_sources']['power-div']['primecert'] = (
            'module\npublic import Lean\npublic meta import Lean\npublic section\n' + raw_div +
            f'\ntheorem result : powDiv 2 {exponent} {n} = 1 := by decide +kernel\n')
        if args.upstream_power:
            record['cases'].append(dict(name='power-upstream', n=n))
            # lean4#13490, commit 86704eea9a8cf46d7f20f4eb2c293cdaae7ac2d7.
            # Copyright (c) 2026 Lean FRO, LLC; Kim Morrison; Apache 2.0.
            # Same kernel definition; renamed and without the runtime extern.
            core = '''
@[expose, semireducible] def powCore (b e m : @& Nat) : Nat :=
  if e = 0 then 1 % m
  else
    let r := powCore (b * b % m) (e / 2) m
    if e % 2 = 1 then r * b % m else r
termination_by e
decreasing_by omega
'''
            record['power_sources']['power-upstream'] = {'hex': (
                'module\npublic import HexPrimality.Cert\npublic import Lean\n'
                'public meta import Lean\npublic section\n' + core +
                f'\ntheorem result : powCore 2 {exponent} {n} = 1 := by decide +kernel\n')}
            record['upstream_power'] = ('Kernel definition only, replayed on Lean 4.34.0; '
                                         'not a native GMP measurement or a Lean 4.35.0 benchmark')
        record['attribution'] = ('powDiv follows PrimeCert/PowMod.lean, Copyright (c) 2022 '
                                 'Bhavik Mehta; file Apache 2.0 notice, root MIT license; full notices in '
                                 'HexArith/Montgomery/Context.lean; source from the retained diagnostic.')
    for system, (cwd, _, path) in locations.items():
        if path.exists():
            raise RuntimeError(f'refusing to overwrite {path}')
        path.parent.mkdir(parents=True, exist_ok=True)
        record['versions'][system] = dict(
            commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=cwd, text=True).strip(),
            toolchain=(cwd/'lean-toolchain').read_text().strip(),
            diff=subprocess.check_output(['git', 'diff', 'HEAD'], cwd=cwd, text=True))

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2)+'\n')

    try:
        for block in range(args.blocks):
            for case in record['cases']:
                for system in (['hex', 'primecert'] if block % 2 == 0 else ['primecert', 'hex']):
                    sources = [r for r in previous['kernel'] if r['case'] == case['name']
                               and r['system'] == system and r.get('arm') == 'replay'
                               and r['status'] == 'ok']
                    if case['name'] in supplied[system]:
                        sources = [{'source': supplied[system][case['name']]}]
                    if args.powers:
                        body = record['power_sources'][case['name']].get(system)
                        sources = [{'source': body}] if body else []
                    if not sources:
                        record['rows'].append(dict(block=block, case=case['name'], system=system,
                                                   status='no-certificate'))
                        save()
                        continue
                    source = sources[0]['source']
                    namespaces = re.findall(r'^namespace (\S+)', source, flags=re.M)
                    result_name = '.'.join([*namespaces, 'result'])
                    source += SUFFIX.replace('RESULT_NAME', result_name).replace('SUBJECT', case['n'])
                    cwd, module, path = locations[system]
                    path.write_text(source)
                    artifact = cwd/'.lake/build/lib/lean'/Path(module.replace('.', '/')+'.olean')
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', '+'+module+':olean'], cwd, 60, cpu)
                    row.update(block=block, case=case['name'], system=system, source=source,
                               source_sha256=hashlib.sha256(source.encode()).hexdigest())
                    if row['status'] == 'ok':
                        row['kernel_nanos'] = int(re.search(r'DIRECT_KERNEL_NS (\d+)', row['stdout'])[1])
                    record['rows'].append(row)
                    save()
                    print(block, case['name'], system, row['status'], row.get('kernel_nanos'), flush=True)
                    if row['status'] != 'ok':
                        raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        for _, _, path in locations.values():
            path.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
