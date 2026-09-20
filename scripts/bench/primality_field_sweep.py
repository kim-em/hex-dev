#!/usr/bin/env python3
"""Reproduce bounded field-prime policy, phase, and factoring diagnostics.

All measurements are pinned, trial-major with adjacent AB/BA arms. Every completed
sample is retained. External factorizations below describe diagnostic inputs only;
no production code reads them. The probe validates each successful certificate.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_cactus import corpus
from scripts.bench.primality_kernel_direct import SUFFIX

PROBE = ROOT / '.lake/build/bin/hexprimality_field_probe'
MODULE = 'HexPrimality.ProofProbe.Curve25519.FieldDiagnostic'
SOURCE = ROOT / 'bench' / (MODULE.replace('.', '/') + '.lean')
RESIDUALS = {
    'secp256k1': 33957291228054575644562761185877073266390894853717235429717263,
    'P-384': 15476043282165938418020047172090971643786229092877237497230280205909552934602070042830819359096205028225297318583,
    'P-384-child': 8913326561311260411185427017705935207065736969962576881302563771106887371009673983,
    'Curve448': 5499843854549273892319703537820711808983983221387696175495353456336512485964978717225063928271651228087,
}
CHILDREN = {
    'secp256k1-child': 205115282021455665897114700593932402728804164701536103180137503955397371,
    'P-384-child': 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097,
}
FACTORIZATIONS = {
    'secp256k1': [132896956044521568488119, 255515944373312847190720520512484175977],
    'P-384': [807145746439, CHILDREN['P-384-child']],
    'P-384-child': [1357291859799823621, 529709925838459440593,
                    12397338596863679689524759770405177749801411],
    'Curve448': [1469495262398780123809, 167773885276849215533569,
                 596242599987116128415063, 37414057161322375957408148834323969],
}
ARMS = {'before': (512, 12, 32768), 'after': (521, 32, 32768)}


def proof_source(n: str, cert: str) -> str:
    return f'''module
public import HexPrimality.Elab
public meta import HexPrimality.Elab
public section

def certificate : Hex.Nat.PrimeCert := {cert}

open Lean Elab Hex.PrimalityTactic in
run_cmd Lean.Elab.Command.liftTermElabM do
  let input ← IO.mkRef certificate
  let cert ← input.get
  let start ← IO.monoNanosNow
  let stx ← certificateSyntax cert
  let _ ← Lean.Elab.Term.elabTerm stx (some (Lean.mkConst ``Hex.Nat.PrimeCert))
  let stop ← IO.monoNanosNow
  logInfo m!"RENDER_ELAB_NS {{stop - start}}"

theorem result : Hex.Nat.Prime {n} :=
  Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)
''' + SUFFIX.replace('RESULT_NAME', 'result').replace('SUBJECT', n)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--blocks', type=int, default=2)
    parser.add_argument('--diagnostics', action='store_true')
    args = parser.parse_args()
    if args.output.exists() or args.blocks < 2 or args.blocks % 2:
        parser.error('use a new output path and an even block count >= 2')
    if SOURCE.exists():
        parser.error(f'temporary probe already exists: {SOURCE}')
    subprocess.run(['lake', 'build', 'hexprimality_field_probe'], cwd=ROOT, check=True)
    cpu = pick()
    sources = ['HexPrimality/Construction.lean', 'HexPrimality/Cert.lean',
               'HexPrimality/Elab.lean', 'HexPrimality/Search.lean',
               'HexPrimality/PMinusOne.lean', 'HexIntFactor/Ecm.lean',
               'bench/HexPrimality/FieldProbe.lean', 'scripts/bench/primality_field_sweep.py']
    record = dict(host=platform.node(), cpu=cpu, affinity=sorted(os.sched_getaffinity(0)),
                  toolchain=(ROOT/'lean-toolchain').read_text().strip(),
                  commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                  source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
                  executable_sha256=hashlib.sha256(PROBE.read_bytes()).hexdigest(),
                  protocol='fixed trial-major adjacent AB/BA; all completed samples retained',
                  timing='native construction includes self-check, excludes formatting; '
                         'render/elaboration excludes proof replay; direct kernel recheck expands '
                         'local dependencies and drains pending checks; see probe sources',
                  arms=ARMS, cases=corpus(), samples=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        args.output.write_text(json.dumps(record, indent=2) + '\n')

    def run(command, **fields):
        row = dict(command=list(map(str, command)), load_before=os.getloadavg(), **fields)
        result = subprocess.run(['taskset', '-c', str(cpu), *map(str, command)],
                                cwd=ROOT, capture_output=True, text=True,
                                env=dict(os.environ, LEAN_NUM_THREADS='1'))
        row.update(stdout=result.stdout, stderr=result.stderr, returncode=result.returncode,
                   load_after=os.getloadavg())
        record['samples'].append(row)
        save()
        if result.returncode:
            raise RuntimeError(f'probe failed: {row}')
        return row

    certs = {}
    try:
        for block in range(args.blocks):
            order = ['before', 'after'] if block % 2 == 0 else ['after', 'before']
            for case in record['cases']:
                name, n = case['name'], case['n']
                for arm in order:
                    row = run([PROBE, 'construction', n, *ARMS[arm]],
                              phase='construction', block=block, case=name, arm=arm)
                    row['result'] = json.loads(row['stdout'])
                    save()
                    if row['result']['status'] == 'ok':
                        cert = row['result']['certificate']
                        previous = certs.setdefault((name, arm), cert)
                        if previous != cert:
                            raise RuntimeError('unstable certificate')
                    print(block, name, arm, row['result']['status'], flush=True)
                for arm in order:
                    cert = certs.get((name, arm))
                    if cert is None:
                        continue  # No constructed proof: replay is unavailable, not zero cost.
                    source = proof_source(n, cert)
                    SOURCE.write_text(source)
                    artifact = ROOT/'.lake/build/lib/lean'/Path(MODULE.replace('.', '/')+'.olean')
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', MODULE], phase='render-and-replay',
                              block=block, case=name, arm=arm, source=source)
                    for tag in ['RENDER_ELAB_NS', 'DIRECT_KERNEL_NS']:
                        row[tag] = int(re.search(tag + r' (\d+)', row['stdout'])[1])
                    row['source_bytes'] = len(source.encode())
                    row['olean_bytes'] = artifact.stat().st_size
                    save()
        if args.diagnostics:
            record['diagnostic_factorizations'] = FACTORIZATIONS
            for name, factors in FACTORIZATIONS.items():
                run([PROBE, 'validate', RESIDUALS[name], *factors],
                    phase='factor-validation', case=name)
            for case in record['cases']:
                if case['name'] not in ['secp256k1', 'P-384', 'Curve448', 'P-521']:
                    continue
                for arm, budget in [('bits-only', (521, 12, 32768)), ('after', ARMS['after'])]:
                    run([PROBE, 'trace', case['n'], *budget], phase='trace', case=case['name'], arm=arm)
            for name, n in CHILDREN.items():
                run([PROBE, 'trace', n, *ARMS['after']], phase='trace', case=name, arm='after')
            for block in range(args.blocks):
                for name, n in RESIDUALS.items():
                    for bound in ([4096, 32768] if block % 2 == 0 else [32768, 4096]):
                        run([PROBE, 'ecm', n, bound, 8], phase='ecm', case=name,
                            block=block, bound=bound, curves=8)
                for name, n in CHILDREN.items():
                    for steps in ([32768, 262144] if block % 2 == 0 else [262144, 32768]):
                        run([PROBE, 'construction', n, 521, 32, steps], phase='rho',
                            case=name, block=block, steps=steps)
        save()
    finally:
        SOURCE.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
