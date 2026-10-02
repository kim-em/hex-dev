#!/usr/bin/env python3
"""Retain ECPP operation profiles with perf, samply and the standard filter."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/bench'))
from cpu_lease import cpu_lease

CASES = [('transcript-length', 'Hex.ECPPBench.runReplay', 4096),
         ('row-vectors', 'Hex.ECPPBench.runParse', 4096),
         ('supplied-certificates', 'runConvert512', 0),
         ('native-production', 'runNativeHard', 0)]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--profiler-root', type=Path, required=True)
    parser.add_argument('--only', nargs='+', choices=[c[0] for c in CASES])
    parser.add_argument('--target-nanos', default=10000000000, type=int)
    parser.add_argument('--scalar-bits', default=4096, type=int)
    args = parser.parse_args()
    if args.output.exists():
        parser.error('preserve completed profile records; choose a new output')
    cpu, lease = cpu_lease()
    exe = ROOT / '.lake/build/bin/hexecpp_bench'
    report = dict(source=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  cpu=cpu, host=os.uname().nodename, platform=platform.platform(),
                  executable_sha256=digest(exe),
                  sources={str(p.relative_to(ROOT)): digest(p) for p in
                           [ROOT / 'scripts/profile/ecpp.py', ROOT / 'bench/HexECPP/Bench.lean',
                            *sorted((ROOT / 'HexECPP').glob('*.lean'))]},
                  profiler_source=subprocess.check_output(
                      ['git', '-C', str(args.profiler_root), 'rev-parse', 'HEAD'], text=True).strip(),
                  commands=[], profiles=[])

    def save():
        args.output.write_text(json.dumps(report, indent=2) + '\n')

    def run(command, env=None):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, env=env)
        report['commands'].append(dict(command=command, returncode=result.returncode,
                                       stdout=result.stdout, stderr=result.stderr))
        save()
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result.stdout

    try:
        report['samply'] = run(['samply', '--version']).strip()
        report['perf'] = run(['perf', '--version']).strip()
        for family, name, param in CASES:
            if args.only and family not in args.only:
                continue
            if family == 'transcript-length':
                param = args.scalar_bits
            directory = Path('/tmp') / (args.output.stem + '-' + family)
            directory.mkdir(exist_ok=False)
            anchor = directory / 'anchor.json'
            anchor.write_text(json.dumps(dict(wall_ns_at_spawn=time.time_ns(),
                                              mono_ns_at_spawn=time.monotonic_ns())))
            sidecar = directory / 'timed.jsonl'
            env = dict(os.environ, LEAN_BENCH_PROFILE_KERNEL='1',
                       LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(sidecar))
            run(['perf', 'record', '--clockid', 'mono', '-e', 'cycles:u', '-F', '999',
                 '--call-graph', 'dwarf', '-o', str(directory / 'perf.data'), '--',
                 'taskset', '-c', str(cpu), str(exe), '_child', '--bench', name,
                 '--param', str(param), '--target-nanos', str(args.target_nanos)], env=env)
            raw = directory / 'samply.json.gz'
            run(['samply', 'import', '--save-only', '--no-open', '--unstable-presymbolicate',
                 '-o', str(raw), str(directory / 'perf.data')])
            samples = run(['perf', 'script', '--ns', '-F', 'pid,tid,time,event',
                           '-i', str(directory / 'perf.data')])
            (directory / 'samples.txt').write_text(samples)
            normalized = directory / 'normalized.json.gz'
            run(['python3', 'scripts/profile/normalize_perf.py', '--profile', str(raw),
                 '--perf-script', str(directory / 'samples.txt'), '--spawn-anchor', str(anchor),
                 '--output', str(normalized)])
            filtered = directory / 'filtered.json.gz'
            diagnostics = directory / 'diagnostics.json'
            run(['python3', str(args.profiler_root / 'scripts/filter_samply.py'),
                 '--samply-json', str(normalized), '--sidecar', str(sidecar),
                 '--spawn-anchor', str(anchor), '--out', str(filtered),
                 '--diagnostics', str(diagnostics), '--label-filter', 'kernel'])
            symbols = directory / 'symbols.json'
            run(['python3', 'scripts/profile/elf_symbols.py', str(filtered),
                 '--output', str(symbols)])
            summary = args.output.parent / (args.output.stem + '-profile-' + family + '.json')
            run(['python3', 'scripts/profile/summarize_profile.py', str(filtered),
                 '--symbols', str(symbols), '--diagnostics', str(diagnostics),
                 '--thread', 'hexecpp_bench', '--top', '25', '--output', str(summary)])
            report['profiles'].append(dict(family=family, target=name, param=param,
                raw_directory=str(directory), summary=str(summary), summary_sha256=digest(summary),
                diagnostics=json.loads(diagnostics.read_text()), loadavg=list(os.getloadavg())))
            save()
            print(family, 'profiled', flush=True)
    except BaseException as error:
        report['error'] = str(error)
        save()
        raise
    finally:
        lease.close()


if __name__ == '__main__':
    main()
