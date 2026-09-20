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
    if phase == 'quotient':
        for rank in ('Full', 'Deficient'):
            for op in ('produce', 'prepare', 'finish', 'check'):
                case = PREFIX + 'Quotient.' + op + rank
                yield op + rank, ['run', case]
    elif phase == 'poly-references':
        for block in range(6):
            for carrier in ('RatPoly', 'Mv'):
                for rank in ('', 'Deficient'):
                    for size in (4, 8, 12):
                        for op in ('Second', 'Check'):
                            native = PREFIX + f'run{carrier}{rank}{op}{size}'
                            external = PREFIX + f'Comparison.{carrier}.{rank or "Full"}.{op.lower()}{size}'
                            arms = [native, external] if block % 2 == 0 else [external, native]
                            yield f'{block}-{carrier}{rank}{op}{size}', ['compare', *arms, '--repeats', '1']
    elif phase == 'integer':
        for family in families:
            for op in ('RowReduce', 'RankCert', 'CheckRank'):
                case = PREFIX + 'run' + op + family
                yield case.rsplit('.', 1)[1], ['run', case]
    elif phase == 'attribution':
        for family in families:
            for op in ('Second', 'Certify', 'Witness'):
                case = PREFIX + op + '.' + family[0].lower() + family[1:]
                yield op + family, ['run', case]
    elif phase == 'polynomial':
        for carrier in ('RatPoly', 'Mv'):
            for rank in ('', 'Deficient'):
                for size in (4, 8, 12):
                    for op in ('Rank', 'Cert', 'Check', 'Second', 'Certify'):
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


def expected_hash(function, param):
    """Independent output contract for the scalar integer schedules."""
    name = function.removeprefix(PREFIX).lower()
    if name.startswith('quotient.prepare'):
        return None  # Full prepared-data hash: checked for agreement at each rung.
    if name.startswith('quotient.'):
        return '0xb' if '.check' in name else hex(param // 2 if 'deficient' in name else param)
    if name.startswith('runcheckrank'):
        return '0xb'  # Lean's Hashable Bool true.
    if 'lowrank2at' in name:
        rank = 2
    elif 'lowrank8at' in name:
        rank = 8
    elif 'deficientminusone' in name:
        rank = param - 1
    elif 'deficienthalf' in name:
        rank = param // 2
    elif 'dense' in name:
        rank = param
    else:
        raise ValueError('unknown parametric output contract: ' + function)
    return hex(rank)  # These small Nat hashes are the values themselves.


def output_errors(export):
    """Malformed exports are failed observations, never a lost schedule tail."""
    errors = []
    try:
        data = json.loads(export.read_text())
        if not data['results']:
            errors.append('empty results')
        for measurement in data['results']:
            name = measurement['function']
            points = measurement['points']
            if not points:
                errors.append('empty measurement: ' + name)
            if any(point['status'] != 'ok' for point in points):
                errors.append('non-ok sample: ' + name)
            if measurement['kind'] == 'fixed':
                if (not measurement.get('hashes_agree') or
                    measurement.get('expected_hash_check', {}).get('status') != 'match'):
                    errors.append('fixed output mismatch: ' + name)
            else:
                hashes = {}
                for point in points:
                    if point['status'] != 'ok':
                        continue
                    param, actual = point['param'], point['result_hash']
                    expected = expected_hash(name, param)
                    if not actual or (expected is not None and actual != expected) or (
                            param in hashes and actual != hashes[param]):
                        errors.append('parametric output mismatch: ' + name)
                        break
                    hashes[param] = actual
    except (OSError, ValueError, KeyError, TypeError) as error:
        errors.append('invalid export: ' + str(error))
    return errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=('integer', 'attribution', 'comparisons', 'polynomial', 'protocol', 'quotient', 'poly-references'))
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--bench', type=Path, default=ROOT / '.lake/build/bin/hexrank_bench')
    parser.add_argument('--python', default=sys.executable)
    parser.add_argument('--family', choices=FAMILIES, action='append', help='Subset for an incremental tranche; omitted means every family.')
    parser.add_argument('--target-inner-nanos', type=int, help='Explicit parametric batch-resolution override, recorded in every command.')
    parser.add_argument('--case', help='Run only the command containing this exact registered name; retain a separate output directory.')
    args = parser.parse_args()
    if args.family and args.phase in ('polynomial', 'protocol', 'quotient', 'poly-references'):
        parser.error('--family is only meaningful for integer, attribution and comparisons')
    if args.target_inner_nanos is not None and (args.target_inner_nanos <= 0 or args.phase not in ('integer', 'attribution', 'quotient')):
        parser.error('--target-inner-nanos requires a positive duration and a parametric phase')
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    bench = args.bench.resolve()
    cpu = pick()
    os.sched_setaffinity(0, {cpu})
    env = dict(os.environ, HEX_RANK_BENCH_PYTHON=args.python)
    schedule = [(label, [str(bench), *command, '--export-file', str(out / f'{label}.json')])
                for label, command in commands(args.phase, args.family or FAMILIES)]
    if args.target_inner_nanos is not None:
        for _, command in schedule:
            command += ['--target-inner-nanos', str(args.target_inner_nanos)]
    if args.case:
        schedule = [(label, command) for label, command in schedule if args.case in command]
        if not schedule:
            parser.error('case is not in the selected phase/family schedule')
    sources = ('bench/HexRank/Bench/Quotient.lean', 'HexRank/PolyProduce.lean', 'bench/HexRank/Bench.lean', 'HexRank/Produce.lean',
               'scripts/oracle/rank_bench.py', 'scripts/oracle/rank_carriers.py',
               'scripts/bench/rank_measure.py', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain')
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
            errors = output_errors(out / f'{label}.json')
            record = {'output_errors': errors, 'label': label, 'command': command, 'exit_code': result.returncode,
                      'started_epoch': started, 'wall_seconds': time.time() - started, 'load_after': os.getloadavg()}
            history.write(json.dumps(record) + '\n')
            history.flush()
            print(label, result.returncode, flush=True)
            if result.returncode or errors:
                failures.append(label)
    (out / 'completion.json').write_text(json.dumps({
        'completed': len(schedule), 'scheduled': len(schedule), 'failures': failures,
        'load_at_end': os.getloadavg()}, indent=2) + '\n')
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
