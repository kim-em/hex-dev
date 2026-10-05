#!/usr/bin/env python3
"""Capture the fixed nested clean/eager comparison, retaining every attempt."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
PARAMETERS = [(depth, steps) for depth in (1, 2) for steps in (2, 4, 8, 16)]
TRIALS = 6
TARGET_NANOS = 500_000_000


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def benchmark(depth, steps, arm):
    return ('Hex.RealClosure.NestedNormalization.Measure.Depth' + str(depth)
            + '.' + ('clean' if arm == 'A' else 'eager') + str(steps))


def schedule():
    return [(trial, depth, steps, arm) for trial in range(TRIALS)
            for depth, steps in PARAMETERS for arm in ('AB' if trial % 2 == 0 else 'BA')]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--oracle-python', type=Path, required=True)
    args = parser.parse_args()
    interpreter = args.oracle_python.absolute()  # Preserve the venv interpreter path.
    destination = args.output.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('capture artifacts must be outside the frozen checkout')
    destination.mkdir(parents=True, exist_ok=False)
    os.chdir(ROOT)
    manifest = destination / 'manifest.json'
    record = dict(status='running', host=platform.node(), platform=platform.platform(),
                  parameters=PARAMETERS, trials=TRIALS, target_inner_nanos=TARGET_NANOS,
                  child_timeout_seconds=600, warmup_first_iter=True,
                  schedule='trial-major; depth1 then depth2; steps2/4/8/16; adjacent alternating AB/BA',
                  arms=dict(A='clean', B='eager'), commands=[], measurements=[],
                  python_version=sys.version, oracle_python=str(interpreter),
                  protocol_sha256=digest(ROOT / 'reports/bench-results/real-closure-nested-protocol.md'),
                  capture_script_sha256=digest(Path(__file__)),
                  analyzer_sha256=digest(ROOT / 'scripts/bench/analyze_real_closure_nested.py'),
                  oracle_sha256=digest(ROOT / 'scripts/oracle/real_closure_nested_normalization.py'))

    def save():
        manifest.write_text(json.dumps(record, indent=2) + '\n')

    def run(command, *, timeout=600, check=True):
        argv = list(map(str, command))
        index = len(record['commands'])
        output, errors = destination / f'{index}.stdout', destination / f'{index}.stderr'
        began = time.monotonic_ns()
        incomplete = False
        with output.open('w') as out, errors.open('w') as err:
            process = subprocess.Popen(argv, stdout=out, stderr=err, start_new_session=True)
            try:
                code = process.wait(timeout=timeout)
            except BaseException:
                incomplete = True
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                raise
            finally:
                record['commands'].append(dict(argv=argv, exit_code=process.returncode,
                    incomplete=incomplete, elapsed_ns=time.monotonic_ns()-began,
                    stdout=output.name, stderr=errors.name))
                save()
        if check and code != 0:
            raise RuntimeError(f'command failed: {argv}')
        return output

    lease = None
    try:
        record['commit'] = run(['git', 'rev-parse', 'HEAD']).read_text().strip()
        if run(['git', 'status', '--porcelain']).read_text().strip():
            raise RuntimeError('measurement source is dirty')
        record['lean_version'] = run(['lake', 'env', 'lean', '--version']).read_text().strip()
        record['cpu_info'] = run(['lscpu', '--json']).read_text()
        packages = json.loads((ROOT / 'lake-manifest.json').read_text())['packages']
        record['dependency_pins'] = {p['name']: p.get('rev') for p in packages}
        package = next(p for p in packages if p['name'].strip('«»') == 'lean-bench')
        checkout = ROOT / '.lake/packages/lean-bench'
        if run(['git', '-C', checkout, 'rev-parse', 'HEAD']).read_text().strip() != package['rev']:
            raise RuntimeError('lean-bench checkout disagrees with its pin')
        if run(['git', '-C', checkout, 'status', '--porcelain']).read_text().strip():
            raise RuntimeError('lean-bench checkout is dirty')
        run(['lake', 'build', 'hexrealclosure_nested_normalization'], timeout=None)
        snapshot = destination / 'hexrealclosure_nested_normalization'
        shutil.copy2(ROOT / '.lake/build/bin/hexrealclosure_nested_normalization', snapshot)
        record['executable_sha256'] = digest(snapshot)
        record['oracle_version'] = run([interpreter, '-c',
            'from importlib.metadata import version; print(version("python-flint"))']).read_text().strip()
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        record.update(cpu=cpu, affinity=sorted(os.sched_getaffinity(0)), load=os.getloadavg())
        hashes = {}
        # Fresh ordinary outputs bind the snapshotted binary to exact field values.
        for depth, steps in PARAMETERS:
            fixtures = []
            hashes[f'{depth}:{steps}'] = {}
            for arm in 'AB':
                policy = 'clean' if arm == 'A' else 'eager'
                fixture = run([snapshot, depth, steps, policy, 'plain'])
                rows = [json.loads(line) for line in fixture.read_text().splitlines() if line.startswith('{')]
                if len(rows) != 1 or (rows[0]['depth'], rows[0]['steps'], rows[0]['eager']) != (depth, steps, arm == 'B'):
                    raise RuntimeError('functional endpoint names a different parameter or policy')
                hashes[f'{depth}:{steps}'][arm] = f'0x{rows[0]["hash"]:x}'
                fixtures.append(fixture)
            run([interpreter, ROOT / 'scripts/oracle/real_closure_nested_normalization.py', *fixtures])
        record['expected_hashes'] = hashes
        run([snapshot, 'verify'])
        for trial, depth, steps, arm in schedule():
            name = benchmark(depth, steps, arm)
            attempt = dict(trial=trial, depth=depth, steps=steps, arm=arm,
                           order='AB' if trial % 2 == 0 else 'BA', load=os.getloadavg())
            # Record even an interrupted child in the measurement inventory.
            attempt['output'] = f'{len(record["commands"])}.stdout'
            record['measurements'].append(attempt)
            save()
            output = run([snapshot, '_child', '--bench', name, '--fixed',
                          '--min-total-nanos', TARGET_NANOS], check=False)
            attempt['exit_code'] = record['commands'][-1]['exit_code']
            rows = [json.loads(line) for line in output.read_text().splitlines() if line.startswith('{')]
            attempt['rows'] = rows
            save()
            if attempt['exit_code'] != 0 or len(rows) != 1:
                raise RuntimeError('measurement process failed or emitted multiple rows')
            row = rows[0]
            if (row.get('status') != 'ok' or row.get('result_hash') != hashes[f'{depth}:{steps}'][arm]
                    or row.get('function') != name or row.get('kind') != 'fixed'
                    or row.get('env', {}).get('git_commit') != record['commit']
                    or row.get('env', {}).get('git_dirty') is not False
                    or row.get('total_nanos', 0) < TARGET_NANOS or row.get('inner_repeats', 0) <= 0):
                raise RuntimeError('measurement failed its result, source or timing binding')
        if (run(['git', 'rev-parse', 'HEAD']).read_text().strip() != record['commit']
                or run(['git', 'status', '--porcelain']).read_text().strip()
                or digest(snapshot) != record['executable_sha256']):
            raise RuntimeError('source or executable changed during capture')
        record['status'] = 'completed'
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        record['artifacts'] = {p.name: digest(p) for p in destination.iterdir() if p.is_file() and p != manifest}
        save()
        if lease is not None:
            lease.close()


if __name__ == '__main__':
    main()
