#!/usr/bin/env python3
"""Retain source, fresh elaboration, warm kernel, and native language comparisons.

Run from hex-dev with a built PrimeCert checkout at the pinned revision. Uses
Lake throughout; generated measurement modules are removed on exit. All samples
are retained, in fixed trial-major order with reversed adjacent arms.
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
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.primality_kernel_direct import SUFFIX
from scripts.bench.primality_primecert_compare import fresh_build

PIN = '0803c2f6bd289c09704c7d352bb8fcf770cbb9b2'
TEMPLATES = ROOT / 'scripts/bench/certificate_language'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primecert-checkout', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--blocks', type=int, default=4)
    args = parser.parse_args()
    if args.output.exists() or args.blocks < 2 or args.blocks % 2:
        parser.error('use a new output and an even block count >= 2')
    pc = args.primecert_checkout.resolve()
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=pc, text=True).strip() != PIN:
        parser.error(f'PrimeCert must be at {PIN}')
    cpu = pick()
    curve = (ROOT / 'bench/HexPrimality/ProofProbe/Curve25519/Literal.lean').read_text()
    curve = curve.split('def certificate : Hex.Nat.PrimeCert :=', 1)[1].split('\nend ', 1)[0].strip()
    named = (ROOT / 'conformance/HexPrimality/CertificateProducer.lean').read_text()
    named = named.split('def curve : Hex.Nat.PrimeCert :=', 1)[1].split('\nend ', 1)[0].strip()
    cases = [
        ('Curve25519', str(2**255 - 19), curve, named,
         (TEMPLATES / 'Curve25519.lean').read_text().split('theorem result', 1)[1].split(':=', 1)[1].strip()),
        ('Repeated', '17', 'Hex.Nat.PrimeCert.pock 17 [(3, 3, .small 2)]',
         'let two : Hex.Nat.PrimeCert := .small 2; .pock 17 [(3, 4 - 1, two)]',
         'prime_cert% [small 2, pock (17, 3, 2 ^ 4)]'),
        ('Sieve', '197', 'Hex.Nat.PrimeCert.pock3Sieve 197 1 6 0 2 [(2, 1, .small 2)]',
         'let two : Hex.Nat.PrimeCert := .small 2; .pock3Sieve 197 1 6 0 2 [(2, 1, two)]',
         'PrimeCert.pocklington3_certK 197 2 2 2 [] .lt (by decide +kernel)'),
    ]
    locations = {
        'hex': (ROOT, 'HexPrimality.ProofProbe.Curve25519.Language',
                ROOT / 'bench/HexPrimality/ProofProbe/Curve25519/Language.lean'),
        'primecert': (pc, 'PrimeCert.Comparator.Language', pc / 'PrimeCert/Comparator/Language.lean'),
    }
    for _, _, path in locations.values():
        if path.exists():
            raise RuntimeError(f'refusing to overwrite {path}')
        path.parent.mkdir(parents=True, exist_ok=True)
    record = dict(schema='hex-primality-language/1', cpu=cpu, host=platform.node(),
                  protocol='fixed trial-major schedule, reverse adjacent arms in odd blocks; retain all samples',
                  fresh_timing='Lake build of fresh module including imports and elaboration; no direct-kernel instrumentation',
                  kernel_timing='warm Kernel.check of fully expanded local proof against its goal, with negative controls',
                  primecert_commit=PIN, versions={}, samples=[], native=[], sources={})
    for system, (cwd, _, _) in locations.items():
        record['versions'][system] = dict(toolchain=(cwd/'lean-toolchain').read_text().strip(),
            commit=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=cwd, text=True).strip())
    record['diff_sha256'] = hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'], cwd=ROOT)).hexdigest()
    record['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2) + '\n')

    try:
        # Warm/build dependencies before measurements; no samples are discarded.
        for system, (cwd, module, path) in locations.items():
            imports = ('HexPrimality.Elab' if system == 'hex' else 'PrimeCert')
            path.write_text(f'module\npublic import {imports}\npublic import Lean\npublic meta import Lean\n')
            subprocess.run(['lake', 'build', '+'+module+':deps'], cwd=cwd, check=True, capture_output=True)
        for block in range(args.blocks):
            for case, n, literal, producer, pc_proof in cases:
                arms = ['literal', 'producer', 'primecert']
                if case == 'Curve25519':
                    arms.insert(0, 'search')
                for arm in (arms if block % 2 == 0 else reversed(arms)):
                    system = 'primecert' if arm == 'primecert' else 'hex'
                    cwd, module, path = locations[system]
                    imports = ('public import PrimeCert\npublic import PrimeCert.SieveBase\npublic meta import PrimeCert.Meta.SieveLookup'
                               if system == 'primecert' else 'public import HexPrimality.Elab')
                    prefix = ('module\n' + imports + '\npublic import Lean\npublic meta import Lean\npublic section\n'
                              'set_option maxRecDepth 65536\nset_option exponentiation.threshold 512\n')
                    if arm == 'primecert':
                        proof = pc_proof
                    elif arm == 'literal':
                        proof = f'Hex.Nat.prime_of_checkPrimeAt (c := {literal}) (by decide +kernel)'
                    elif arm == 'search':
                        proof = 'by primality?'
                    else:
                        proof = f'by primality? using ({producer})'
                    subject = f'Nat.Prime {n}' if system == 'primecert' else f'Hex.Nat.Prime {n}'
                    source = prefix + f'theorem result : {subject} :=\n  {proof}\n'
                    key = case + '/' + arm
                    record['sources'][key] = dict(source=source, source_bytes=len(source.encode()),
                        proof_bytes=len(proof.encode()), sha256=hashlib.sha256(source.encode()).hexdigest())
                    path.write_text(source)
                    row = fresh_build(cwd, module, cpu)
                    row.update(block=block, case=case, arm=arm)
                    record['samples'].append(row)
                    save()
                    path.write_text(source + SUFFIX.replace('RESULT_NAME', 'result').replace('SUBJECT', n))
                    checked = fresh_build(cwd, module, cpu)
                    row['kernel_nanos'] = int(re.search(r'DIRECT_KERNEL_NS (\d+)', checked['output'] if 'output' in checked else checked['stdout'])[1])
                    row['kernel_stdout'] = checked['stdout']
                    row['kernel_stderr'] = checked['stderr']
                    save()
                    print(f'{block} {key}: fresh {row["wall_nanos"]/1e9:.3f}s kernel {row["kernel_nanos"]/1e6:.3f}ms', flush=True)
            # Native comparison uses the existing constructor and the same
            # certificate supplied as data; parsing/startup excluded internally.
            for arm in (['construction', 'supplied'] if block % 2 == 0 else ['supplied', 'construction']):
                cmd = [str(ROOT/'.lake/build/bin/hexprimality_policy_probe')]
                cmd += ['construction', str(2**255-19)] if arm == 'construction' else ['curve-supplied']
                before = os.getloadavg()
                proc = subprocess.run(['taskset', '-c', str(cpu), *cmd], capture_output=True, text=True, check=True)
                result = json.loads(proc.stdout)
                if result['status'] != 'ok':
                    raise RuntimeError(proc.stdout)
                record['native'].append(dict(block=block, arm=arm, result=result,
                    load_before=before, load_after=os.getloadavg()))
                save()
        certificates = {r['result']['certificate'] for r in record['native']}
        if len(certificates) != 1:
            raise RuntimeError('native arms did not produce the same certificate')
    finally:
        for _, _, path in locations.values():
            path.unlink(missing_ok=True)
        save()


if __name__ == '__main__':
    main()
