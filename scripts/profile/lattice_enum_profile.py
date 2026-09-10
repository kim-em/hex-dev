#!/usr/bin/env python3
"""Capture and summarize timed-region lattice profiles with lean-bench-samply.

Set LEAN_BENCH_SAMPLY_HOME to a checkout of kim-em/lean-bench-samply. The
postprocessor must pass its calibration, sample-count and sensitivity checks.
Raw filtered stacks, symbols, diagnostics and source hashes remain auditable.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import tempfile

from factor_sampling_profile import Symbolicator, analyse


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exe', type=Path, default=Path('.lake/build/bin/hexlatticeenum_bench'))
    parser.add_argument('--results', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--param', type=int, default=2048)
    args = parser.parse_args()
    sampler = Path(os.environ.get('LEAN_BENCH_SAMPLY_HOME', str(Path.home() / 'projects/lean-bench-samply')))
    orchestrator = sampler / 'scripts/profile_bench.py'
    if not orchestrator.exists():
        parser.error('set LEAN_BENCH_SAMPLY_HOME to the lean-bench-samply checkout')
    args.out.mkdir(parents=True, exist_ok=True)
    exe = args.exe.resolve()
    parameters = {'runRank': 128, 'runCube': 13, 'runRadius': 2048, 'runShear': 128,
                  'runHeight': None}
    names = [r['function'] for r in json.loads(args.results.read_text())['results']
             if r['function'].startswith('Hex.LatticeEnumBench.runAmbient')
             or r['function'].rsplit('.', 1)[-1] in parameters]
    summaries = []
    for name in names:
        stem = name.rsplit('.', 1)[-1]
        param = parameters.get(stem, args.param)
        out = (args.out / f'{stem}.json.gz').resolve()
        # lean-bench's profile subcommand has no fixed-benchmark support yet.
        # The bench supplies profile-height with that same timed-region
        # protocol; retain the sampler's unmodified filtering checks.
        with tempfile.TemporaryDirectory(prefix='hex-lattice-profile-') as tmp:
            wrapped = exe
            if param is None:
                wrapped = Path(tmp) / 'fixed-child'
                wrapped.write_text('#!/bin/sh\nexec ' + shlex.quote(str(exe)) +
                    ' profile-height\n')
                wrapped.chmod(0o755)
            command = ['python3', str(orchestrator), '--bench-exe', str(wrapped),
                       '--bench-name', name, '--param', str(param or 0),
                       '--target-nanos', '1000000000', '--out', str(out),
                       '--samply-args', '--rate 999 --unstable-presymbolicate']
            run = subprocess.run(command, text=True, capture_output=True)
        (args.out / f'{stem}.log').write_text(run.stdout + run.stderr)
        run.check_returncode()
        diagnostics = json.loads(Path(str(out) + '.diagnostics.json').read_text())
        if diagnostics['confidence'] != 'passed':
            raise ValueError(f'low-confidence profile: {name}')
        symbols = Path(str(out).removesuffix('.json.gz') + '.json.syms.json')
        with gzip.open(out) as handle:
            profile = json.load(handle)
        summary = {'function': name, 'param': param, 'diagnostics': diagnostics,
                   **analyse(profile, Symbolicator(symbols), 20, diagnostics['bench_thread_name'])}
        (args.out / f'{stem}.summary.json').write_text(json.dumps(summary, indent=2) + '\n')
        summaries.append(summary)
        print(f'{stem}: {summary["samples"]} samples; calibration and sensitivity passed', flush=True)
    source_files = sorted(Path('HexLatticeEnum').glob('*.lean')) + [Path('bench/HexLatticeEnum/Bench.lean')]
    manifest = {'exe_sha256': hashlib.sha256(exe.read_bytes()).hexdigest(),
                'sources': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files},
                'sampler_commit': subprocess.check_output(['git', '-C', str(sampler), 'rev-parse', 'HEAD'], text=True).strip(),
                'profiles': names}
    (args.out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'{len(summaries)} profiles captured; {sum(r["samples"] for r in summaries)} timed-region samples')


if __name__ == '__main__':
    main()
