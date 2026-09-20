#!/usr/bin/env python3
"""Capture HexRank's four representative timed-region profiles.

Use perf's user-space cycle sampler, import with samply, then apply the shared
clock normalization, kernel-region filter and bounded ELF symbolization tools.
All captures are retained. Raw profiles stay local; commit the small summaries.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick

CASES = (
    ('dense-full-rank', 'runRankCertDense', 64),
    ('low-rank-large-coefficients', 'runRankCertLowRank8At1024', 128),
    ('rank-deficient-by-construction', 'runRankCertDeficientHalfShifted', 128),
    ('polynomial', 'runMvCert12', 0),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--profiler-root', type=Path, required=True)
    parser.add_argument('--bench', type=Path, default=ROOT / '.lake/build/bin/hexrank_bench')
    parser.add_argument('--quotient', action='store_true', help='Profile the separate native quotient producer at dimension 32.')
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    bench = args.bench.resolve()
    cpu = pick()
    os.sched_setaffinity(0, {cpu})
    meta = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
            'cpu': cpu, 'load': os.getloadavg(), 'binary': str(bench),
            'binary_sha256': hashlib.sha256(bench.read_bytes()).hexdigest(),
            'profiler_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=args.profiler_root, text=True).strip(),
            'samply_version': subprocess.check_output(['samply', '--version'], text=True).strip(),
            'perf_version': subprocess.check_output(['perf', '--version'], text=True).strip(),
            'commands': [], 'environment_overrides': [], 'failures': []}
    def run(command, env=None):
        meta['commands'].append(command)
        meta['environment_overrides'].append({key: env[key] for key in
            ('LEAN_BENCH_PROFILE_KERNEL', 'LEAN_BENCH_TIMED_REGIONS_SIDECAR')} if env else {})
        (out / 'metadata.json').write_text(json.dumps(meta, indent=2) + '\n')
        result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        with (directory / 'commands.txt').open('a') as log:
            log.write(json.dumps(command) + '\n' + result.stdout + result.stderr + '\n')
        result.check_returncode()
        return result.stdout
    cases = (('quotient-witness', 'Quotient.produceFull', 32),) if args.quotient else CASES
    for family, name, param in cases:
        directory = out / family
        directory.mkdir()
        try:
            anchor = directory / 'spawn-anchor.json'
            anchor.write_text(json.dumps({'wall_ns_at_spawn': time.time_ns(), 'mono_ns_at_spawn': time.monotonic_ns()}))
            run(['perf', 'record', '--clockid', 'mono', '-e', 'cycles:u', '-F', '999',
                 '--call-graph', 'dwarf', '-o', str(directory / 'perf.data'), '--', str(bench),
                 '_child', '--bench', 'Hex.RankBench.' + name, '--param', str(param),
                 '--target-nanos', '3000000000', '--cache-mode', 'warm'],
                env=dict(os.environ, LEAN_BENCH_PROFILE_KERNEL='1',
                         LEAN_BENCH_TIMED_REGIONS_SIDECAR=str(directory / 'timed.jsonl')))
            run(['samply', 'import', '--save-only', '--no-open', '--unstable-presymbolicate',
                 '-o', str(directory / 'samply.json.gz'), str(directory / 'perf.data')])
            samples = run(['perf', 'script', '--ns', '-F', 'pid,tid,time,event', '-i', str(directory / 'perf.data')])
            (directory / 'perf-samples.txt').write_text(samples)
            run([sys.executable, str(ROOT / 'scripts/profile/normalize_perf.py'),
                 '--profile', str(directory / 'samply.json.gz'), '--perf-script', str(directory / 'perf-samples.txt'),
                 '--spawn-anchor', str(anchor), '--output', str(directory / 'normalized.json.gz')])
            run([sys.executable, str(args.profiler_root / 'scripts/filter_samply.py'),
                 '--samply-json', str(directory / 'normalized.json.gz'), '--sidecar', str(directory / 'timed.jsonl'),
                 '--spawn-anchor', str(anchor), '--out', str(directory / 'filtered.json.gz'),
                 '--diagnostics', str(directory / 'diagnostics.json'), '--label-filter', 'kernel'])
            run([sys.executable, str(ROOT / 'scripts/profile/elf_symbols.py'), str(directory / 'filtered.json.gz'),
                 '--output', str(directory / 'symbols.json')])
            run([sys.executable, str(ROOT / 'scripts/profile/summarize_profile.py'), str(directory / 'filtered.json.gz'),
                 '--symbols', str(directory / 'symbols.json'), '--diagnostics', str(directory / 'diagnostics.json'),
                 '--thread', 'hexrank_bench', '--top', '25', '--output', str(directory / 'summary.json')])
            print(family, 'profiled', flush=True)
        except subprocess.CalledProcessError as error:
            meta['failures'].append({'family': family, 'command': error.cmd, 'exit_code': error.returncode})
            print(family, 'failed', error.returncode, flush=True)
        finally:
            meta['load_after'] = os.getloadavg()
            (out / 'metadata.json').write_text(json.dumps(meta, indent=2) + '\n')
    return bool(meta['failures'])


if __name__ == '__main__':
    raise SystemExit(main())
