#!/usr/bin/env python3
"""Capture the registered six-round adjacent rational root route comparison."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease

CASES = ("Zero", "Constant", "Multiplicity1", "Multiplicity2", "Multiplicity4", "Multiplicity8")
PAIRS = (('generic', 'canonical'),)
SOURCES = ('bench/HexRealClosure/TrivialMeasurements.lean',
           'scripts/bench/collect_real_closure_trivial.py',
           'scripts/oracle/real_closure_trivial_measurements.py',
           'scripts/bench/cpu_lease.py',
           'reports/bench-results/real-closure-trivial/protocol.md',
           'conformance-fixtures/HexRealClosure/trivial-measurements.jsonl')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    parser.add_argument('--oracle-python', type=Path, required=True)
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('retain raw evidence outside the frozen checkout')
    if git('status', '--porcelain'):
        parser.error('commit the protocol and source before measurement')
    destination.mkdir(parents=True, exist_ok=False)
    environment = dict(os.environ, LEAN_ABORT_ON_PANIC='1')
    record = dict(status='preparing', source=git('rev-parse', 'HEAD'),
                  host=platform.node(), platform=platform.platform(), started_utc=utc(),
                  cases=CASES, pairs=PAIRS, rounds=6, observations=[],
                  schedule='trial-major, zero/constant/multiplicities 1/2/4/8, adjacent pair alternates AB/BA',
                  process_timeout_seconds=3600,
                  source_hashes={name: digest(ROOT / name) for name in SOURCES},
                  toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                  lake_manifest=json.loads((ROOT / 'lake-manifest.json').read_text()),
                  compiler_override=os.environ.get('LEAN_CC'), panic_abort=True, commands=[])
    manifest = destination / 'metadata.json'
    def save():
        manifest.write_text(json.dumps(record, indent=2) + '\n')
    def run(argv, label, timeout=3600, acceptable=(0,)):
        argv = list(map(str, argv))
        item = dict(command=argv, started_utc=utc(), load_before=list(os.getloadavg()),
                    stdout=label + '.stdout', stderr=label + '.stderr')
        record['commands'].append(item)
        save()
        started = time.monotonic()
        with (destination / item['stdout']).open('w') as out, \
                (destination / item['stderr']).open('w') as err:
            process = subprocess.Popen(argv, cwd=ROOT, stdout=out, stderr=err,
                                       env=environment, start_new_session=True)
            try:
                item['exit_code'] = process.wait(timeout=timeout)
            except BaseException:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                item.update(exit_code=process.returncode, incomplete=True)
                raise
            finally:
                item.update(elapsed_seconds=time.monotonic()-started,
                            load_after=list(os.getloadavg()))
                save()
        if item['exit_code'] not in acceptable:
            raise RuntimeError(f'failed command retained: {label}')
        return item
    lease = None
    save()
    try:
        for name in SOURCES:
            target = destination / 'sources' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        if record['compiler_override']:
            compiler = Path(record['compiler_override'])
            record['compiler_override_sha256'] = digest(compiler)
            shutil.copy2(compiler, destination / 'compiler-override')
            run([compiler, '--version'], 'compiler-version')
        package = ROOT / '.lake/packages/lean-bench'
        actual_pin = subprocess.check_output(['git', '-C', package, 'rev-parse', 'HEAD'], text=True).strip()
        packages = record['lake_manifest']['packages']
        expected_pin = next(item['rev'] for item in packages if item['name'].strip('«»') == 'lean-bench')
        if actual_pin != expected_pin or subprocess.check_output(
                ['git', '-C', package, 'status', '--porcelain'], text=True).strip():
            raise RuntimeError('lean-bench source differs from its clean pinned revision')
        record['lean_bench_pin'] = actual_pin
        run(['lake', 'build', 'hexrealclosure_trivial_bench'], 'build')
        executable = destination / 'hexrealclosure_trivial_bench'
        shutil.copy2(ROOT / '.lake/build/bin/hexrealclosure_trivial_bench', executable)
        record['binary_sha256'] = digest(executable)
        recipe = ROOT / '.lake/build/bin/hexrealclosure_trivial_bench.rsp'
        record['link_recipe_sha256'] = digest(recipe)
        shutil.copy2(recipe, destination / 'link.rsp')
        run(['lake', 'env', 'lean', '--version'], 'lean-version')
        run(['lscpu', '--json'], 'cpu-info')
        functional = run([executable, 'emit'], 'functional')
        fixture = ROOT / 'conformance-fixtures/HexRealClosure/trivial-measurements.jsonl'
        if (destination / functional['stdout']).read_bytes() != fixture.read_bytes():
            raise RuntimeError('fresh output differs from committed matched-arm fixture')
        run([args.oracle_python, ROOT / 'scripts/oracle/real_closure_trivial_measurements.py',
             destination / functional['stdout']], 'oracle')
        if git('rev-parse', 'HEAD') != record['source'] or git('status', '--porcelain'):
            raise RuntimeError('source changed before measurement')
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
        record.update(status='measuring', cpu=cpu, affinity=sorted(os.sched_getaffinity(0)))
        save()
        for trial in range(6):
            for case in CASES:
                for pair in PAIRS:
                    arms = pair if trial % 2 == 0 else tuple(reversed(pair))
                    for arm in arms:
                        label = f'{trial:02d}-{case}-{arm}'
                        export = destination / (label + '.json')
                        item = run([executable, 'run',
                                    f'Hex.RealClosure.TrivialMeasurements.{case}.{arm}',
                                    '--repeats', '1', '--min-total-seconds', '0.5',
                                    '--export-file', export], label, acceptable=(0, 2))
                        record['observations'].append(dict(trial=trial, case=case, pair=pair[0],
                                                           arm=arm, export=export.name,
                                                           command_index=len(record['commands'])-1,
                                                           exit_code=item['exit_code']))
                        save()
                        print(f'{label}: exit {item["exit_code"]}', flush=True)
        if git('rev-parse', 'HEAD') != record['source'] or git('status', '--porcelain'):
            raise RuntimeError('source changed during capture')
        record['status'] = 'completed'
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        record['ended_utc'] = utc()
        record['artifacts'] = {str(path.relative_to(destination)): digest(path)
                               for path in destination.rglob('*') if path.is_file() and path != manifest}
        save()
        if lease is not None:
            lease.close()


if __name__ == '__main__':
    main()
