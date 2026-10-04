#!/usr/bin/env python3
"""Retain a fixed trial-major, adjacent AB/BA clean/eager arithmetic study."""
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

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'scripts/bench'))
from cpu_lease import cpu_lease


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--oracle-python', type=Path, required=True)
    args = parser.parse_args()
    destination = args.output.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('measurement artifacts must remain outside the frozen checkout')
    destination.mkdir(parents=True, exist_ok=False)
    os.chdir(ROOT)
    manifest = destination / 'manifest.json'
    record = dict(status='running', host=platform.node(), platform=platform.platform(),
                  sizes=[2,4,8,16], trials=5, target_inner_nanos=500000000,
                  schedule='trial-major; degree order 2,4,8,16; adjacent AB/BA alternating by trial',
                  arms=dict(A='clean', B='eager'), commands=[], measurements=[])
    def save():
        manifest.write_text(json.dumps(record, indent=2)+'\n')
    def run(command, *, timeout=600):
        argv = list(map(str, command))
        index = len(record['commands'])
        output = destination / f'{index}.stdout'
        errors = destination / f'{index}.stderr'
        began = time.monotonic_ns()
        with output.open('w') as out, errors.open('w') as err:
            process = subprocess.Popen(argv, stdout=out, stderr=err, start_new_session=True)
            try:
                code = process.wait(timeout=timeout)
            except BaseException:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
                record['commands'].append(dict(argv=argv, exit_code=process.returncode,
                    incomplete=True, elapsed_ns=time.monotonic_ns()-began, stdout=str(output), stderr=str(errors)))
                save()
                raise
        record['commands'].append(dict(argv=argv, exit_code=code,
            elapsed_ns=time.monotonic_ns()-began, stdout=str(output), stderr=str(errors)))
        save()
        if code != 0:
            raise RuntimeError(f'command failed: {argv}')
        return output
    lease = None
    try:
        record['commit'] = run(['git','rev-parse','HEAD']).read_text().strip()
        if run(['git','status','--porcelain']).read_text().strip():
            raise RuntimeError('measurement source is dirty')
        record['dirty'] = False
        record['lean_version'] = run(['lake','env','lean','--version']).read_text().strip()
        record['cpu_info'] = run(['lscpu','--json']).read_text()
        dependencies = json.loads((ROOT/'lake-manifest.json').read_text())
        record['dependency_pins'] = {p['name']: p.get('rev') for p in dependencies['packages']}
        bench_package = next(p for p in dependencies['packages'] if p['name'].strip('«»') == 'lean-bench')
        if run(['git','-C',ROOT/'.lake/packages/lean-bench','rev-parse','HEAD']).read_text().strip() != bench_package['rev']:
            raise RuntimeError('lean-bench checkout disagrees with its source pin')
        if run(['git','-C',ROOT/'.lake/packages/lean-bench','status','--porcelain']).read_text().strip():
            raise RuntimeError('lean-bench checkout is dirty')
        run(['lake','build','hexrealclosure_normalization_bench'])
        snapshot = destination / 'hexrealclosure_normalization_bench'
        shutil.copy2(ROOT/'.lake/build/bin/hexrealclosure_normalization_bench',snapshot)
        record['executable_sha256'] = digest(snapshot)
        record['oracle_python'] = str(args.oracle_python.resolve())
        record['oracle_version'] = run([args.oracle_python,'-c',
            'import z3; from importlib.metadata import version; print(version("python-flint"), z3.get_version_string())']).read_text().strip()
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0,{cpu})
        record.update(cpu=cpu, affinity=sorted(os.sched_getaffinity(0)), load=os.getloadavg())
        for degree in record['sizes']:
            fixture = run([snapshot,'storage',degree])
            run([args.oracle_python,'scripts/oracle/real_closure_normalization.py',fixture])
        for trial in range(record['trials']):
            order = ['A','B'] if trial % 2 == 0 else ['B','A']
            for degree in record['sizes']:
                for arm in order:
                    name = 'Hex.RealClosure.Normalization.run' + ('Clean' if arm=='A' else 'Eager')
                    load = os.getloadavg()
                    output = run([snapshot,'_child','--bench',name,'--param',degree,
                        '--target-nanos',record['target_inner_nanos'],'--cache-mode','warm'])
                    rows = [json.loads(line) for line in output.read_text().splitlines() if line.startswith('{')]
                    record['measurements'].append(dict(trial=trial, degree=degree, arm=arm,
                        order=''.join(order), load=load, rows=rows, output=str(output)))
                    save()
                    if len(rows)!=1 or rows[0].get('status')!='ok' or rows[0].get('result_hash')!='0x1':
                        raise RuntimeError('measurement failed its complete arithmetic result check')
                    if rows[0].get('function') != name or rows[0].get('param') != degree:
                        raise RuntimeError('measurement row names a different arm or parameter')
                    env = rows[0].get('env',{})
                    if env.get('git_commit')!=record['commit'] or env.get('git_dirty') is not False:
                        raise RuntimeError('measurement row is not bound to the clean source')
        if run(['git','rev-parse','HEAD']).read_text().strip()!=record['commit'] or run(['git','status','--porcelain']).read_text().strip():
            raise RuntimeError('source changed during measurement')
        record['status'] = 'completed'
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        record['artifacts']={p.name:digest(p) for p in destination.iterdir() if p.is_file() and p!=manifest}
        save()
        if lease is not None:
            lease.close()


if __name__ == '__main__':
    main()
