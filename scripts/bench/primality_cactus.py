#!/usr/bin/env python3
"""Bounded shared-host comparison: Hex construction, FLINT/PARI, and PrimeCert replay.

Run inside a Python environment with python-flint and cypari2. Kernel comparison
uses a separate, unmodified PrimeCert checkout; all generated Lean modules are
removed on exit. Every completed sample and timeout is retained. No oracle data
is supplied to Hex construction.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick

PREFIX = 'HexPrimality.ProofProbe.Curve25519.Cactus'
HEADER = 'module\npublic import HexPrimality.Elab\npublic meta import HexPrimality.Elab\npublic section\n'


def worker(system: str, n: str) -> None:
    if system == 'flint':
        import flint
        value = flint.fmpz(n)
        version = {'python-flint': flint.__version__, 'flint': flint.__FLINT_VERSION__}
        start = time.perf_counter_ns()
        answer = value.is_prime()
    else:
        import cypari2
        pari = cypari2.Pari()
        value = pari(n)
        version = {'pari': str(pari('version()'))}
        start = time.perf_counter_ns()
        answer = value.isprime()
    elapsed = time.perf_counter_ns() - start
    print(json.dumps({'status': 'ok' if answer else 'composite', 'nanos': elapsed,
                      'version': version}))


def corpus() -> list[dict]:
    cases = []
    for bits in (31, 61, 123, 256, 511, 512):
        source = (ROOT / f'scripts/bench/primecert/Bit{bits}.lean.in').read_text()
        n = int(re.search(r'Nat.Prime\s+(\d+)', source)[1])
        cases.append({'name': f'family-{bits}', 'n': str(n), 'bits': bits,
                      'primecert': source})
    for name, n in [('Curve25519', 2**255-19), ('secp256k1', 2**256-2**32-977),
                    ('P-256', 2**256-2**224+2**192+2**96-1),
                    ('P-384', 2**384-2**128-2**96+2**32-1),
                    ('Curve448', 2**448-2**224-1), ('P-521', 2**521-1)]:
        cases.append({'name': name, 'n': str(n), 'bits': n.bit_length()})
    return cases


def run(command: list[str], cwd: Path, timeout: float, cpu: int) -> dict:
    start = time.perf_counter()
    before = os.getloadavg()
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    with subprocess.Popen(['taskset', '-c', str(cpu), *command], cwd=cwd, env=env,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          start_new_session=True) as proc:
        timed_out = False
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            stdout, stderr = proc.communicate()
    return {'status': 'timeout' if timed_out else ('ok' if proc.returncode == 0 else 'error'),
            'seconds': time.perf_counter()-start, 'returncode': proc.returncode,
            'load_before': before, 'load_after': os.getloadavg(), 'stdout': stdout,
            'stderr': stderr, 'command': command}


def native_source(n: str) -> str:
    return HEADER + f'''
#eval show IO Unit from do
  let input ← IO.mkRef ({n} : Nat)
  let n ← input.get
  let start ← IO.monoNanosNow
  let result ← IO.mkRef (Hex.Nat.Construction.run n (Hex.Rand.ofSeed n))
  let result ← result.get
  let stop ← IO.monoNanosNow
  let fields := [("nanos", toJson (stop - start))]
  match result with
  | .error f => IO.println ("CACTUS " ++ (Lean.Json.mkObj
      (fields ++ [("status", toJson "exhausted"), ("attempts", toJson f.attempts)])).compress)
  | .ok s =>
    let cert ← IO.mkRef s.cert.raw
    let cert ← cert.get
    let checkStart ← IO.monoNanosNow
    let checked ← IO.mkRef (Hex.Nat.checkPrime cert)
    let checked ← checked.get
    let checkStop ← IO.monoNanosNow
    unless checked do throw (IO.userError "invalid certificate")
    IO.println ("CACTUS " ++ (Lean.Json.mkObj (fields ++
      [("status", toJson "ok"), ("attempts", toJson s.attempts),
       ("check_nanos", toJson (checkStop - checkStart)),
       ("certificate", toJson (reprStr cert))])).compress)
'''.replace('toJson', 'Lean.toJson')


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worker', choices=['flint', 'pari'])
    p.add_argument('--n')
    p.add_argument('--primecert-checkout', type=Path)
    p.add_argument('--output', type=Path)
    p.add_argument('--blocks', type=int, default=2)
    p.add_argument('--timeout', type=float, default=60)
    args = p.parse_args()
    if args.worker:
        worker(args.worker, args.n)
        return
    if not args.output or not args.primecert_checkout or args.blocks < 2 or args.blocks % 2:
        p.error('provide output, PrimeCert checkout, and an even block count >= 2')
    pc = args.primecert_checkout.resolve()
    cases = corpus()
    examples = (pc / 'PrimeCertTest/PrimeListTest.lean').read_text()
    for name, expr in [('Curve25519', '2 ^ 255 - 19'), ('Curve448', '2 ^ 448 - 2 ^ 224 - 1')]:
        case = next(c for c in cases if c['name'] == name)
        start = examples.index(f'example : Nat.Prime ({expr})')
        end = examples.index('\n\n', start)
        body = examples[start:end].replace('example :', 'theorem result :', 1)
        case['primecert'] = ('module\npublic import PrimeCert\npublic section\n'
            'set_option maxRecDepth 2048\nset_option exponentiation.threshold 512\n' + body + '\n')
    cpu = pick()
    record = {'schema': 'hex-primality-cactus/1', 'host': platform.node(),
              'cpu': cpu, 'blocks': args.blocks, 'timeout': args.timeout,
              'hex_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
              'hex_toolchain': (ROOT/'lean-toolchain').read_text().strip(),
              'primecert_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=pc, text=True).strip(),
              'primecert_toolchain': (pc/'lean-toolchain').read_text().strip(),
              'protocol': 'trial-major adjacent systems; reverse systems and baseline/replay arms in odd blocks; all completed samples retained',
              'cases': cases, 'native': [], 'kernel': [],
              'source_sha256': {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest()
                 for f in sorted((ROOT/'HexPrimality').glob('*.lean'))}}
    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(record, indent=2)+'\n')
    native_path = ROOT/'bench'/Path(PREFIX.replace('.', '/')+'.lean')
    hex_path = native_path.with_name('CactusReplay.lean')
    pc_path = pc/'PrimeCert/Comparator/Cactus.lean'
    pc_path.parent.mkdir(parents=True, exist_ok=True)
    paths = [native_path, hex_path, pc_path]
    if any(path.exists() for path in paths):
        raise RuntimeError('refusing to overwrite an existing generated probe')
    try:
        for block in range(args.blocks):
            for case in cases:
                for system in (['hex', 'flint', 'pari'] if block % 2 == 0 else ['pari', 'flint', 'hex']):
                    if system == 'hex':
                        native_path.write_text(native_source(case['n']))
                        row = run(['lake', 'build', PREFIX], ROOT, args.timeout, cpu)
                        matches = re.findall(r'CACTUS (\{.*\})', row['stdout'])
                        if row['status'] == 'ok' and matches:
                            row['result'] = json.loads(matches[-1])
                            row['status'] = row['result']['status']
                        elif row['status'] == 'ok':
                            raise RuntimeError('missing Hex measurement')
                    else:
                        row = run([sys.executable, str(Path(__file__).resolve()), '--worker', system,
                                   '--n', case['n']], ROOT, args.timeout, cpu)
                        if row['status'] == 'ok':
                            row['result'] = json.loads(row['stdout'])
                    row.update(block=block, case=case['name'], system=system)
                    record['native'].append(row)
                    save()
                    print('native', block, case['name'], system, row['status'],
                          row.get('result', {}).get('nanos'), flush=True)
                    if row['status'] == 'error':
                        raise RuntimeError(row['stdout']+row['stderr'])
        # Replay only predeclared PrimeCert cases; Hex literals come from the
        # measured deterministic generator, without external factor assistance.
        for block in range(args.blocks):
            for case in [c for c in cases if 'primecert' in c]:
                found = [r['result']['certificate'] for r in record['native']
                         if r['case'] == case['name'] and r['system'] == 'hex' and r['status'] == 'ok']
                if found and len(set(found)) != 1:
                    raise RuntimeError('nondeterministic certificate')
                for system in (['hex', 'primecert'] if block % 2 == 0 else ['primecert', 'hex']):
                    if system == 'hex' and not found:
                        record['kernel'].append(dict(block=block, case=case['name'],
                            system=system, status='no-certificate'))
                        save()
                        continue
                    for arm in (['baseline', 'replay'] if block % 2 == 0 else ['replay', 'baseline']):
                        if system == 'hex':
                            body = HEADER + f'def certificate : Hex.Nat.PrimeCert := {found[0]}\n'
                            if arm == 'replay':
                                body += f'theorem result : Hex.Nat.Prime {case["n"]} :=\n  Hex.Nat.prime_of_checkPrimeAt (c := certificate) (by decide +kernel)\n'
                            path, cwd, module = hex_path, ROOT, PREFIX+'Replay'
                        else:
                            body = case['primecert'] if arm == 'replay' else 'module\npublic import PrimeCert\n'
                            path, cwd, module = pc_path, pc, 'PrimeCert.Comparator.Cactus'
                        path.write_text(body)
                        artifact = cwd/'.lake/build/lib/lean'/Path(module.replace('.', '/')+'.olean')
                        artifact.unlink(missing_ok=True)
                        row = run(['lake', 'build', '+'+module+':olean'], cwd, args.timeout, cpu)
                        row.update(block=block, case=case['name'], system=system, arm=arm,
                                   source=body, source_bytes=len(body.encode()),
                                   olean_bytes=artifact.stat().st_size if artifact.exists() else None)
                        record['kernel'].append(row)
                        save()
                        print('kernel', block, case['name'], system, arm, row['status'], row['seconds'], flush=True)
                        if row['status'] == 'error':
                            raise RuntimeError(row['stdout']+row['stderr'])
    finally:
        for path in paths:
            path.unlink(missing_ok=True)
        save()


if __name__ == '__main__':
    main()
