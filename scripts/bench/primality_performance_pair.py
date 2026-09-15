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
from scripts.bench.primality_cactus import HEADER, native_source, run

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    roots = {'old': args.baseline.resolve(), 'new': ROOT}
    cpu = pick()
    n = str(2**255-19)
    literal = (ROOT/'bench/HexPrimality/ProofProbe/Curve25519/Literal.lean').read_text()
    certificate = literal.split('def certificate : Hex.Nat.PrimeCert :=')[1].split('\nend ')[0]
    sources = {'native': native_source(n),
               'replay': HEADER+'def certificate : Hex.Nat.PrimeCert :=\n'+certificate+
                   '\ntheorem result : Hex.Nat.Prime (2 ^ 255 - 19) :=\n'
                   '  Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)\n',
               'complete': HEADER+'theorem result : Hex.Nat.Prime (2 ^ 255 - 19) := by primality?\n'}
    record = {'cpu': cpu, 'host': platform.node(), 'samples': [],
              'protocol': 'two trial-major blocks, adjacent old/new arms with reversed order; all completed samples retained',
              'versions': {arm: {'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                  'toolchain': (root/'lean-toolchain').read_text().strip(),
                  'sources': {name: hashlib.sha256((root/name).read_bytes()).hexdigest()
                              for name in ('HexPrimality/Sieve.lean', 'HexPrimality/Table.lean', 'HexPrimality/Cert.lean')}}
                  for arm, root in roots.items()}}
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
                    (root/'bench'/relative).write_text(body)
                    artifact = root/'.lake/build/lib/lean'/relative.with_suffix('.olean')
                    artifact.unlink(missing_ok=True)
                    row = run(['lake', 'build', '+'+module+':olean'], root, 60, cpu)
                    row.update(block=block, phase=phase, arm=arm, source=body,
                               source_bytes=len(body.encode()),
                               olean_bytes=artifact.stat().st_size if artifact.exists() else None)
                    if phase == 'native' and row['status'] == 'ok':
                        row['result'] = json.loads(re.findall(r'CACTUS (\{.*\})', row['stdout'])[-1])
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
