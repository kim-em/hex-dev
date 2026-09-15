#!/usr/bin/env python3
"""Adjacent old/new Curve25519 construction, replay, and complete proof builds."""
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
from scripts.bench.primality_cactus import HEADER, interpreted_source, run

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--native-only', action='store_true', help='compare native construction executables')
    args = p.parse_args()
    roots = {'old': args.baseline.resolve(), 'new': ROOT}
    cpu = pick()
    n = str(2**255-19)
    literal = (ROOT/'bench/HexPrimality/ProofProbe/Curve25519/Literal.lean').read_text()
    certificate = literal.split('def certificate : Hex.Nat.PrimeCert :=')[1].split('\nend ')[0]
    sources = {'interpreted-search': interpreted_source(n),
               'replay': HEADER+'def certificate : Hex.Nat.PrimeCert :=\n'+certificate+
                   '\ntheorem result : Hex.Nat.Prime (2 ^ 255 - 19) :=\n'
                   '  Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)\n',
               'complete': HEADER+'theorem result : Hex.Nat.Prime (2 ^ 255 - 19) := by primality?\n'}
    if args.native_only:
        sources = {'native-executable': ''}
    record = {'cpu': cpu, 'host': platform.node(), 'samples': [],
              'protocol': 'two trial-major blocks, adjacent old/new arms with reversed order; all completed samples retained',
              'versions': {arm: {'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  'toolchain': (root/'lean-toolchain').read_text().strip(),
                  'diff_sha256': hashlib.sha256(subprocess.check_output(['git', 'diff', 'HEAD'], cwd=root)).hexdigest(),
                  'sources': {name: hashlib.sha256((root/name).read_bytes()).hexdigest()
                              for name in ('HexPrimality/Sieve.lean', 'HexPrimality/Table.lean', 'HexPrimality/Cert.lean')}}
                  for arm, root in roots.items()}}
    if args.native_only:
        for arm, root in roots.items():
            record['versions'][arm]['probe_sha256'] = hashlib.sha256(
                (root/'bench/HexPrimality/PolicyProbe.lean').read_bytes()).hexdigest()
            record['versions'][arm]['executable_sha256'] = hashlib.sha256(
                (root/'.lake/build/bin/hexprimality_policy_probe').read_bytes()).hexdigest()
    module = 'HexPrimality.ProofProbe.Curve25519.PerformancePair'
    relative = Path(module.replace('.', '/')+'.lean')
    paths = [root/'bench'/relative for root in roots.values()]
    if args.output.exists() or any(path.exists() for path in paths):
        raise RuntimeError('refusing to overwrite a probe or retained record')
    try:
        for block in range(2):
            for phase, body in sources.items():
                for arm in (['old', 'new'] if block == 0 else ['new', 'old']):
                    root = roots[arm]
                    artifact = root/'.lake/build/lib/lean'/relative.with_suffix('.olean')
                    if args.native_only:
                        command = [str(root/'.lake/build/bin/hexprimality_policy_probe'), 'construction', n]
                    else:
                        (root/'bench'/relative).write_text(body)
                        artifact.unlink(missing_ok=True)
                        command = ['lake', 'build', '+'+module+':olean']
                    row = run(command, root, 60, cpu)
                    measured_source = (root/'bench/HexPrimality/PolicyProbe.lean').read_text() if args.native_only else body
                    row.update(block=block, phase=phase, arm=arm, source=measured_source,
                               source_bytes=len(measured_source.encode()),
                               olean_bytes=artifact.stat().st_size if artifact.exists() and not args.native_only else None)
                    if args.native_only and row['status'] == 'ok':
                        row['result'] = json.loads(row['stdout'])
                        row['status'] = row['result']['status']
                    elif phase == 'interpreted-search' and row['status'] == 'ok':
                        row['result'] = json.loads(re.findall(r'CACTUS (\{.*\})', row['stdout'])[-1])
                        row['status'] = row['result']['status']
                    record['samples'].append(row)
                    args.output.write_text(json.dumps(record, indent=2)+'\n')
                    print(block, phase, arm, row['status'], row['seconds'],
                          row.get('result', {}).get('nanos'), flush=True)
                    if row['status'] != 'ok':
                        raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        for path in paths:
            path.unlink(missing_ok=True)

if __name__ == '__main__':
    main()
