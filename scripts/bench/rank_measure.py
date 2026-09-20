#!/usr/bin/env python3
"""Run HexRank's declared LeanBench schedules, retaining all output.

This only orchestrates LeanBench; it does not implement a timing loop or a
verdict. Comparisons run six adjacent AB/BA blocks on the same automatic CPU.
Use distinct output directories for integer, comparisons, polynomial and
protocol phases. Native/comparator fixtures and expected ranks live in Lean.
"""
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
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick

FAMILIES = ('Dense', 'LowRank2At64', 'LowRank8At64', 'LowRank2At1024',
            'LowRank8At1024', 'DeficientMinusOne', 'DeficientHalf', 'DeficientHalfShifted')
SIZES = (16, 24, 32, 48, 64, 96, 128, 192, 256)
PREFIX = 'Hex.RankBench.'


def commands(phase, families):
    if phase == 'integer':
        for family in families:
            for op in ('RowReduce', 'RankCert', 'CheckRank'):
                case = PREFIX + 'run' + op + family
                yield case.rsplit('.', 1)[1], ['run', case]
    elif phase == 'polynomial':
        for carrier in ('RatPoly', 'Mv'):
            for rank in ('', 'Deficient'):
                for size in (4, 8, 12):
                    for op in ('Rank', 'Cert', 'Check'):
                        case = PREFIX + f'run{carrier}{rank}{op}{size}'
                        yield case.rsplit('.', 1)[1], ['run', case, '--repeats', '6']
    elif phase == 'protocol':
        yield 'overhead', ['run', PREFIX + 'runProtocolOverhead']
    else:
        pairs = []
        for family in families:
            for size in SIZES:
                for carrier in ('Int', 'Rat'):
                    stem = f'compare{carrier}{family}{size}'
                    namespace = PREFIX + f'Comparison.{carrier}.{family}.'
                    pairs.append((stem, namespace + f'native{size}', namespace + f'external{size}'))
        for carrier in ('RatPoly', 'Mv'):
            for rank in ('', 'Deficient'):
                for size in (4, 8, 12):
                    stem = f'compare{carrier}{rank}{size}'
                    pairs.append((stem, PREFIX + f'run{carrier}{rank}Rank{size}', PREFIX + f'Comparison.{carrier}.{rank or "Full"}.external{size}'))
        for block in range(6):
            for stem, native, external in pairs:
                arms = [native, external] if block % 2 == 0 else [external, native]
                yield f'{block}-{stem}', ['compare', *arms, '--repeats', '1']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('integer', 'comparisons', 'polynomial', 'protocol'))
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--bench', type=Path, default=ROOT / '.lake/build/bin/hexrank_bench')
    parser.add_argument('--python', default=sys.executable)
    parser.add_argument('--family', choices=FAMILIES, action='append', help='Subset for an incremental tranche; omitted means every family.')
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    bench = args.bench.resolve()
    cpu = pick()
    os.sched_setaffinity(0, {cpu})
    env = dict(os.environ, HEX_RANK_BENCH_PYTHON=args.python)
    schedule = [(label, [str(bench), *command, '--export-file', str(out / f'{label}.json')])
                for label, command in commands(args.phase, args.family or FAMILIES)]
    sources = ('bench/HexRank/Bench.lean', 'HexRank/Produce.lean',
               'scripts/oracle/rank_bench.py', 'scripts/oracle/rank_carriers.py',
               'scripts/bench/rank_measure.py', 'lake-manifest.json', 'lean-toolchain')
    metadata = {'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                'source_sha256': {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in sources},
                'binary_sha256': hashlib.sha256(bench.read_bytes()).hexdigest(),
                'platform': platform.platform(), 'hostname': platform.node(),
                'cpu_description': subprocess.check_output(['lscpu'], text=True),
                'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
                'harness_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT / '.lake/packages/lean-bench', text=True).strip(),
                'cpu': cpu, 'affinity': sorted(os.sched_getaffinity(0)),
                'load_at_start': os.getloadavg(), 'command': sys.argv,
                'cwd': str(ROOT), 'python': args.python, 'schedule': schedule}
    versions = subprocess.run([args.python, str(ROOT / 'scripts/oracle/rank_bench.py')],
                             input='{"op":"versions"}\n', text=True, capture_output=True, check=True, env=env)
    metadata['comparator_versions'] = json.loads(versions.stdout)
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (out / 'source.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD'], cwd=ROOT))
    failures = []
    with (out / 'commands.jsonl').open('w') as history:
        for label, command in schedule:
            started = time.time()
            with (out / f'{label}.txt').open('w') as log:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            errors = []
            export = out / f'{label}.json'
            if not export.exists():
                errors.append('missing export')
            else:
                data = json.loads(export.read_text())
                for measurement in data['results']:
                    if not measurement.get('points'):
                        errors.append('empty measurement: ' + measurement['function'])
                    if any(point['status'] != 'ok' for point in measurement['points']):
                        errors.append('non-ok sample: ' + measurement['function'])
                    if measurement['kind'] == 'fixed' and (
                        not measurement.get('hashes_agree') or
                        measurement.get('expected_hash_check', {}).get('status') != 'match'
                    ):
                        errors.append('fixed output mismatch: ' + measurement['function'])
            record = {'output_errors': errors, 'label': label, 'command': command, 'exit_code': result.returncode,
                      'started_epoch': started, 'wall_seconds': time.time() - started, 'load_after': os.getloadavg()}
            history.write(json.dumps(record) + '\n')
            history.flush()
            print(label, result.returncode, flush=True)
            if result.returncode or errors:
                failures.append(label)
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
