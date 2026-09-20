#!/usr/bin/env python3
"""Bounded offline ECM stage-2 investigation; every completed sample is retained.

No factors from the diagnostic corpus are passed to the constructor. The core
portfolio, experimental provider, certificate self-check, and kernel replay run
in Lean. Python schedules subprocesses and records their outputs only.
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
from scripts.bench.primality_field_sweep import (
    PROBE, MODULE, SOURCE, RESIDUALS, CHILDREN, FACTORIZATIONS, proof_source,
)

# Fixed schedules, chosen before measurement. A larger tier spends 64 curves;
# construction uses eight per residual while preserving its global 1024 attempts.
TIERS = [(4096, 65536, 16), (32768, 524288, 64)]
CONSTRUCTION = (32768, 524288, 8)


def primes_below(limit):
    sieve = bytearray(b'\x01') * limit
    sieve[:2] = b'\x00\x00'
    for p in range(2, int(limit**0.5) + 1):
        if sieve[p]:
            sieve[p*p:limit:p] = b'\x00' * len(range(p*p, limit, p))
    return [p for p in range(2, limit) if sieve[p]]


def scalar_cost(k):
    return 0 if k == 0 else 13 * (k.bit_length() - 1) + 7


def work_bound(b1, b2):
    """Reduced modular multiplications, including squarings; setup adds eight.

    xDouble costs seven, xAdd six. Each nontrivial scalar ladder level
    executes one of each. Sieve, scalar-index arithmetic, additions/remainders,
    and gcd costs are separate; this is not an equal wallclock allocation.
    """
    primes = primes_below(max(b1, b2) + 1)
    stage1 = 8
    for p in primes:
        if p > b1:
            break
        power = p
        while power <= b1 // p:
            power *= p
        stage1 += scalar_cost(power)
    interval = [p for p in primes if b1 < p <= b2]
    if not interval:
        return stage1
    advances = max(0, interval[-1] // 210 - 1)
    stage2 = sum(scalar_cost(j) for j in range(211))
    stage2 += 6 * advances + (1 if advances else 0)
    stage2 += sum(scalar_cost(q) + 1 if q < 210 else 3 for q in interval)
    return stage1 + stage2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--paths-only', action='store_true',
                        help='reuse the residual evidence; measure full construction and traces only')
    parser.add_argument('--curves', type=int, default=CONSTRUCTION[2])
    args = parser.parse_args()
    if not 0 <= args.curves <= 64:
        parser.error('curves must be in [0,64]')
    construction = (*CONSTRUCTION[:2], args.curves)
    tiers = [] if args.paths_only else TIERS
    if args.output.exists() or SOURCE.exists():
        parser.error('output and temporary proof module must not already exist')
    subprocess.run(['lake', 'build', 'hexprimality_field_probe'], cwd=ROOT, check=True)
    cpu = pick()
    sources = ['bench/HexPrimality/FieldProbe.lean',
               'scripts/bench/primality_ecm_sweep.py', 'HexIntFactor/Ecm.lean',
               'HexIntFactor/EcmStage2.lean', 'HexIntFactor/Construction.lean',
               'HexPrimality/Construction.lean', 'HexPrimality/Search.lean',
               'HexPrimality/PMinusOne.lean', 'HexPrimality/Cert.lean',
               'HexPrimality/Elab.lean', 'scripts/bench/primality_field_sweep.py',
               'scripts/bench/primality_kernel_direct.py']
    record = dict(commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'],
                  cwd=ROOT, text=True).strip(), host=platform.node(), cpu=cpu,
                  toolchain=(ROOT/'lean-toolchain').read_text().strip(),
                  source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
                  executable_sha256=hashlib.sha256(PROBE.read_bytes()).hexdigest(),
                  protocol='two fixed trial-major blocks, adjacent AB/BA; no rejected samples',
                  tiers=tiers, construction=construction, samples=[],
                  p_minus_one_stage2='SPEC contract exists; implementation absent in measured sources',
                  diagnostic_factorizations=FACTORIZATIONS, work_allocations=[])
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        args.output.write_text(json.dumps(record, indent=2) + '\n')

    def run(command, **fields):
        row = dict(command=list(map(str, command)), load_before=os.getloadavg(), **fields)
        result = subprocess.run(['taskset', '-c', str(cpu), *row['command']], cwd=ROOT,
                                capture_output=True, text=True,
                                env=dict(os.environ, LEAN_NUM_THREADS='1'))
        row.update(stdout=result.stdout, stderr=result.stderr, returncode=result.returncode,
                   load_after=os.getloadavg())
        record['samples'].append(row)
        save()  # Persist failures before parsing or raising.
        if result.returncode:
            raise RuntimeError(f'probe failed: {row}')
        if result.stdout.startswith('{'):
            row['result'] = json.loads(result.stdout)
            save()
        return row

    run([PROBE, 'verify-ecm2'], phase='verification')
    cases = [c for c in corpus() if c['name'] in ['secp256k1', 'P-384', 'Curve448', 'P-521']]
    for name, factors in FACTORIZATIONS.items():
        run([PROBE, 'validate', RESIDUALS[name], *factors], phase='diagnostic-validation', case=name)
    # Run every scheduled curve even after a success, so the full distribution
    # and all-miss counts do not depend on an early-stop reporting convention.
    for b1, b2, curves in tiers:
        two_work, one_work = work_bound(b1, b2), work_bound(b1, b1)
        total = curves * two_work
        one_curves = total // one_work
        allocation = dict(b1=b1, b2=b2, mult_cap=total,
                          stage2_curves=curves, stage1_curves=one_curves,
                          stage2_per_curve=two_work, stage1_per_curve=one_work,
                          stage1_unused=total-one_curves*one_work)
        record['work_allocations'].append(allocation)
        for block in range(2):
            for name, n in RESIDUALS.items():
                for arm in (['stage1', 'stage2'] if block == 0 else ['stage2', 'stage1']):
                    for sigma in range(6, 6 + (curves if arm == 'stage2' else one_curves)):
                        run([PROBE, 'ecm2', n, sigma, b1, b2 if arm == 'stage2' else b1],
                            phase='residual', case=name, block=block, arm=arm, sigma=sigma,
                            b1=b1, b2=b2 if arm == 'stage2' else b1)
                    print('residual', b1, block, name, arm, flush=True)
    certs = {}
    try:
        for block in range(2):
            order = ['baseline', 'ecm2'] if block == 0 else ['ecm2', 'baseline']
            for case in cases:
                name, n = case['name'], case['n']
                for arm in order:
                    command = ([PROBE, 'construction', n, 521, 32, 32768] if arm == 'baseline'
                               else [PROBE, 'construction2', n, *construction])
                    row = run(command, phase='construction', block=block, case=name, arm=arm)
                    result = row['result']
                    if result['status'] == 'ok':
                        cert = result['certificate']
                        if certs.setdefault((name, arm), cert) != cert:
                            raise RuntimeError('unstable certificate')
                    print('construction', block, name, arm, result['status'], flush=True)
                if (name, 'baseline') in certs and (name, 'ecm2') in certs:
                    if certs[name, 'baseline'] != certs[name, 'ecm2']:
                        raise RuntimeError('supported certificate changed')
                for arm in order:
                    cert = certs.get((name, arm))
                    if cert is None:
                        continue  # Exhaustion has no proof to render or replay.
                    source = proof_source(n, cert)
                    SOURCE.write_text(source)
                    artifact = ROOT/'.lake/build/lib/lean'/Path(MODULE.replace('.', '/')+'.olean')
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', MODULE], phase='render-and-replay',
                              case=name, arm=arm, block=block, source=source)
                    for tag in ['RENDER_ELAB_NS', 'DIRECT_KERNEL_NS']:
                        row[tag] = int(re.search(tag + r' (\d+)', row['stdout'])[1])
                    save()
        # Exact recursive callback traces, outside timed construction samples.
        for case in cases:
            for arm in ['baseline', 'ecm2']:
                command = ([PROBE, 'trace', case['n'], 521, 32, 32768] if arm == 'baseline'
                           else [PROBE, 'trace2', case['n'], *construction])
                run(command, phase='trace', case=case['name'], arm=arm)
        children = dict(CHILDREN)
        for name in ['secp256k1', 'P-384-child', 'Curve448']:
            for index, n in enumerate(FACTORIZATIONS[name]):
                children[f'{name}-factor-{index}'] = n
        # These are independent diagnostic subjects, never inputs to root factor search.
        for name, n in children.items():
            run([PROBE, 'trace2', n, *construction], phase='child-trace', case=name, n=str(n))
            print('child', name, flush=True)
    finally:
        SOURCE.unlink(missing_ok=True)
    save()


if __name__ == '__main__':
    main()
