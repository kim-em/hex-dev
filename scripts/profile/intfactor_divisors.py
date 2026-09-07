#!/usr/bin/env python3
"""Capture public divisor attribution with perf and the standard samply filter."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench import intfactor_phase4 as collector


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--profiler-root', required=True, type=Path)
    args = parser.parse_args()
    attempt = collector.Attempt(args.output)
    directory = attempt.directory
    def run(command, timeout=120):
        return attempt.execute(command, stdin=None, timeout=timeout, allowed=(0,))
    try:
        attempt.record.update(scope='divisor-profile', state_before=collector.host_state(7),
            commit=run(['git', 'rev-parse', 'HEAD']).stdout.strip(),
            dirty_status=run(['git', 'status', '--porcelain']).stdout,
            executable_sha256=collector.sha256(collector.BENCH),
            source_sha256=collector.sha256(collector.ROOT / 'bench/HexIntFactor/Bench.lean'),
            profiler_commit=run(['git', '-C', str(args.profiler_root), 'rev-parse', 'HEAD']).stdout.strip())
        run(['perf', '--version'])
        run(['samply', '--version'])
        anchor = directory / 'spawn-anchor.json'
        anchor.write_text(json.dumps(dict(wall_ns_at_spawn=time.time_ns(),
                                         mono_ns_at_spawn=time.monotonic_ns())))
        run(['perf', 'record', '--clockid', 'mono', '-e', 'cycles:u', '-F', '999',
             '--call-graph', 'dwarf', '-o', str(directory / 'perf.data'), '--',
             'taskset', '-c', '7', 'env',
             f'LEAN_BENCH_TIMED_REGIONS_SIDECAR={directory}/timed-%p.jsonl',
             str(collector.BENCH), '_child', '--bench', 'Hex.IntFactorBench.runDivisors',
             '--param', '32768', '--target-nanos', '5000000000'])
        run(['samply', 'import', '--save-only', '--no-open', '--unstable-presymbolicate',
             '-o', str(directory / 'samply.json.gz'), str(directory / 'perf.data')])
        sidecars = list(directory.glob('timed-*.jsonl'))
        if len(sidecars) != 1:
            raise RuntimeError('expected one profile timed-region sidecar')
        run([sys.executable, str(args.profiler_root / 'scripts/filter_samply.py'),
             '--samply-json', str(directory / 'samply.json.gz'),
             '--sidecar', str(sidecars[0]), '--spawn-anchor', str(anchor),
             '--out', str(directory / 'filtered.json.gz'),
             '--diagnostics', str(directory / 'diagnostics.json'),
             '--label-filter', 'warm-loop'])
        run([sys.executable, str(collector.ROOT / 'scripts/profile/summarize_profile.py'),
             str(directory / 'filtered.json.gz'), '--symbols', str(directory / 'samply.json.syms.json'),
             '--diagnostics', str(directory / 'diagnostics.json'),
             '--thread', 'hexintfactor_be', '--top', '25',
             '--output', str(directory / 'summary.json')])
        attempt.record['status'] = 'profiled'
    except BaseException as error:
        attempt.record.update(status='rejected', error=str(error), error_type=type(error).__name__)
        raise
    finally:
        raw = directory / 'perf.data'
        if raw.exists():
            with raw.open('rb') as source, gzip.open(directory / 'perf.data.gz', 'wb') as target:
                shutil.copyfileobj(source, target)
            raw.unlink()
        attempt.record['state_after'] = collector.host_state(7)
        attempt.record['artifact_sha256'] = {
            p.name: collector.sha256(p) for p in directory.iterdir() if p.is_file()}
        attempt.save()


if __name__ == '__main__':
    main()
