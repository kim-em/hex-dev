#!/usr/bin/env python3
"""Retain one source-bound, untimed worker-count diagnostic per retained degree.

Both ordinary and instrumented processes must reproduce the committed packet.
An independent exact oracle checks that packet. Every command, cap and failure
is retained; the runner never retries or infers a timing/complexity verdict.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.meti_counts import KINDS, check_packet, parse_record
from scripts.bench.real_closure_metitarski_scaling import dependency_pins, digest

DEGREES = [3, 5, 7, 9]
SOURCES = [
    'bench/HexRealClosure/Phase4.lean',
    'scripts/bench/real_closure_meti_counts.py',
    'scripts/bench/meti_counts.py',
    'scripts/bench/build_meti_counts.py',
    'scripts/bench/build_nested_normalization_counts.py',
    'scripts/bench/ffi/meti_counts.c',
    'scripts/bench/cpu_lease.py',
    'scripts/bench/real_closure_metitarski_scaling.py',
    'scripts/oracle/real_closure_metitarski_scaling.py',
    'scripts/oracle/real_algebraic_qqbar.py',
    'conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl',
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--oracle-python', type=Path, required=True)
    args = parser.parse_args()
    destination = args.output.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('retain evidence outside the checkout')
    destination.mkdir(parents=True, exist_ok=False)
    os.chdir(ROOT)
    oracle_python = args.oracle_python.absolute()
    record = dict(
        schema=1, status='preparing', started_utc=datetime.now(timezone.utc).isoformat(),
        host=platform.node(), platform=platform.platform(), python=sys.version,
        degrees=DEGREES, paper_degree=3, derived_degrees=[5, 7, 9],
        kinds=list(KINDS), commands=[], rows=[],
        source_hashes={name: digest(ROOT / name) for name in SOURCES},
        purpose='diagnostic generated-C worker entries and loop tests',
        inside='runtime input read, first complete native second-stage producer including internal validation, single-root match',
        outside='degree15 predecessor, selection, input polynomial, explicit final equation/replay checks, serialization',
        warmup=False, timing_inference=False,
        schedule='one ordinary validation and one instrumented process per degree in 3/5/7/9 order',
        retries=0, process_cap_seconds=600)
    manifest = destination / 'manifest.json'

    def save():
        pending = destination / 'manifest.pending'
        pending.write_text(json.dumps(record, indent=2) + '\n')
        pending.replace(manifest)

    def run(argv, timeout=600):
        argv = list(map(str, argv))
        index = len(record['commands'])
        stdout, stderr = destination / f'{index}.stdout', destination / f'{index}.stderr'
        item = dict(argv=argv, stdout=stdout.name, stderr=stderr.name,
                    started_utc=datetime.now(timezone.utc).isoformat(),
                    load=list(os.getloadavg()), timeout_seconds=timeout)
        record['commands'].append(item)
        save()
        began = time.monotonic_ns()
        with stdout.open('w') as out, stderr.open('w') as err:
            process = subprocess.Popen(argv, stdout=out, stderr=err, start_new_session=True)
            try:
                item['exit_code'] = process.wait(timeout=timeout)
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
                item.update(exit_code=process.returncode, incomplete=True)
                raise
            finally:
                item['elapsed_ns'] = time.monotonic_ns() - began
                save()
        if item['exit_code'] != 0:
            raise RuntimeError(f'diagnostic command failed: {argv}')
        return stdout, stderr

    lease = None
    affinity = os.sched_getaffinity(0)
    save()
    try:
        record['commit'] = run(['git', 'rev-parse', 'HEAD'])[0].read_text().strip()
        if run(['git', 'status', '--porcelain'])[0].read_text().strip():
            raise RuntimeError('diagnostic source must be committed and clean')
        for name in SOURCES:
            path = destination / 'sources' / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, path)
        record['dependency_pins'] = dependency_pins(json.loads(
            (ROOT / 'lake-manifest.json').read_text())['packages'])
        record['lean_version'] = run(['lake', 'env', 'lean', '--version'])[0].read_text().strip()
        record['cpu_info'] = run(['lscpu', '--json'])[0].read_text()
        run([sys.executable, 'scripts/bench/build_meti_counts.py', destination / 'build'], timeout=1800)
        built = json.loads((destination / 'build/build.json').read_text())
        if built['status'] != 'completed' or built['source_head'] != record['commit']:
            raise RuntimeError('instrumented build differs from captured source')
        ordinary = destination / 'ordinary'
        shutil.copy2(ROOT / '.lake/build/bin/hexrealclosure_phase4', ordinary)
        diagnostic = destination / 'build/metitarski-counts'
        if (digest(ordinary) != built['ordinary_binary_sha256'] or
                digest(diagnostic) != built['diagnostic_binary_sha256']):
            raise RuntimeError('executable snapshot differs from build metadata')
        record['ordinary_sha256'] = digest(ordinary)
        record['diagnostic_sha256'] = digest(diagnostic)
        record['instrumented_kinds'] = built['instrumented_kinds']
        record['oracle_version'] = run([oracle_python, '-c',
            'import flint; print(flint.__version__,flint.__FLINT_VERSION__)'])[0].read_text().strip()
        if record['oracle_version'] != '0.9.0 3.6.0':
            raise RuntimeError('diagnostic requires pinned python-flint and FLINT')
        fixtures = {json.loads(line)['degree']: line + '\n' for line in
                    (ROOT / 'conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl').read_text().splitlines()}
        if sorted(fixtures) != DEGREES:
            raise RuntimeError('functional fixture inventory changed')
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        record.update(status='collecting', cpu=cpu, affinity=sorted(os.sched_getaffinity(0)))
        save()
        for degree in DEGREES:
            control, control_errors = run([ordinary, 'metitarski', 'counts', degree])
            check_packet(control.read_text(), fixtures[degree], degree)
            events = [line for line in control_errors.read_text().splitlines() if line.startswith('METI ')]
            if events != ['METI BEGIN', 'METI END']:
                raise RuntimeError('ordinary observer-mode control has a different region')
            output, errors = run([diagnostic, 'metitarski', 'counts', degree])
            check_packet(output.read_text(), fixtures[degree], degree)
            counts = parse_record(errors.read_text())
            oracle, _ = run([oracle_python, 'scripts/oracle/real_closure_metitarski_scaling.py', output])
            checked = json.loads(oracle.read_text())
            if checked['degree'] != degree or checked['real_roots'] != 1 or checked['multiplicity'] != 1:
                raise RuntimeError('independent oracle result changed')
            record['rows'].append(dict(degree=degree, ordinary=control.name, fixture=output.name,
                                       counters=errors.name, oracle=oracle.name, observed=counts))
            save()
        if (run(['git', 'rev-parse', 'HEAD'])[0].read_text().strip() != record['commit'] or
                run(['git', 'status', '--porcelain'])[0].read_text().strip()):
            raise RuntimeError('source changed during capture')
        if digest(ordinary) != record['ordinary_sha256'] or digest(diagnostic) != record['diagnostic_sha256']:
            raise RuntimeError('executable snapshot changed during capture')
        record['status'] = 'completed'
    except BaseException as error:
        record.update(status='failed', error=repr(error))
        raise
    finally:
        record['ended_utc'] = datetime.now(timezone.utc).isoformat()
        record['artifacts'] = {str(p.relative_to(destination)): digest(p)
                               for p in destination.rglob('*') if p.is_file() and p != manifest}
        save()
        os.sched_setaffinity(0, affinity)
        if lease is not None:
            lease.close()


if __name__ == '__main__':
    main()
