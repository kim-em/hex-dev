#!/usr/bin/env python3
"""Retain the fixed six-trial MetiTarski second-stage degree ladder."""
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
sys.path.insert(0,str(ROOT))
from scripts.bench.cpu_lease import cpu_lease

DEGREES = [3,5,7,9]
FUNCTION = 'Hex.RealClosure.Bench.measureMetiSecond'
SOURCE_PATHS = ['bench/HexRealClosure/Bench.lean','bench/HexRealClosure/Phase4.lean',
                'scripts/bench/real_closure_metitarski_scaling.py',
                'scripts/oracle/real_closure_metitarski_scaling.py',
                'scripts/bench/analyze_real_closure_metitarski_scaling.py',
                'scripts/bench/cpu_lease.py','scripts/oracle/real_algebraic_qqbar.py']


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream,'sha256').hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--oracle-python',type=Path,required=True)
    args = parser.parse_args()
    destination = args.output.resolve()
    if destination == ROOT or ROOT in destination.parents:
        parser.error('retain evidence outside the frozen checkout')
    destination.mkdir(parents=True,exist_ok=False)
    oracle_python = args.oracle_python.absolute()
    os.chdir(ROOT)
    record = dict(schema=1,status='preparing',started_utc=datetime.now(timezone.utc).isoformat(),
                  host=platform.node(),platform=platform.platform(),python=sys.version,
                  degrees=DEGREES,trials=6,commands=[],
                  schedule='lean-bench custom schedule; six trial-major rounds, 3/5/7/9 in each',
                  hypothesis='n^3 over one fixed algebraic coefficient context; no bit-complexity bound',
                  inference='descriptive shared-host medians and complete ranges; no significance test',
                  reruns='one fixed capture; retain every completed or failed point; no automatic rerun',
                  target_inner_nanos=500000000,child_timeout_seconds=120,
                  process_timeout_seconds=3600,
                  inside='input-function IO.Ref read, full coefficient-prefix extraction/normalization, native complete second-stage root production, root-count check and ordinary harness hash/consumer',
                  outside='degree15 root construction, least-root checks, input powers and initial forcing/hash, one explicit warm-up per child, functional queries and serialization',
                  source_hashes={name:digest(ROOT/name) for name in SOURCE_PATHS})
    manifest = destination/'manifest.json'
    def save():
        manifest.write_text(json.dumps(record,indent=2)+'\n')
    def run(argv,timeout=600,acceptable=(0,)):
        argv = list(map(str,argv))
        index = len(record['commands'])
        output, errors = destination/f'{index}.stdout',destination/f'{index}.stderr'
        began = time.monotonic_ns()
        item = dict(argv=argv,stdout=output.name,stderr=errors.name,load=list(os.getloadavg()),
                    started_utc=datetime.now(timezone.utc).isoformat(),acceptable_exit_codes=list(acceptable))
        record['commands'].append(item)
        save()
        with output.open('w') as out,errors.open('w') as err:
            process = subprocess.Popen(argv,stdout=out,stderr=err,start_new_session=True)
            try:
                item['exit_code'] = process.wait(timeout=timeout)
            except BaseException:
                try: os.killpg(process.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                process.wait()
                item.update(exit_code=process.returncode,incomplete=True)
                raise
            finally:
                item['elapsed_ns'] = time.monotonic_ns()-began
                save()
        if item['exit_code'] not in acceptable:
            raise RuntimeError(f'command failed: {argv}')
        return output
    lease = None
    save()
    try:
        record['commit'] = run(['git','rev-parse','HEAD']).read_text().strip()
        if run(['git','status','--porcelain']).read_text().strip():
            raise RuntimeError('measurement source is dirty')
        record['dirty'] = False
        for name in SOURCE_PATHS:
            path = destination/'sources'/name
            path.parent.mkdir(parents=True,exist_ok=True)
            shutil.copy2(ROOT/name,path)
        record['lean_version'] = run(['lake','env','lean','--version']).read_text().strip()
        record['cpu_info'] = run(['lscpu','--json']).read_text()
        dependencies = json.loads((ROOT/'lake-manifest.json').read_text())
        record['dependency_pins'] = {p['name']:p.get('rev') for p in dependencies['packages']}
        pin = record['dependency_pins']['lean-bench']
        if run(['git','-C',ROOT/'.lake/packages/lean-bench','rev-parse','HEAD']).read_text().strip() != pin:
            raise RuntimeError('lean-bench checkout differs from source pin')
        if run(['git','-C',ROOT/'.lake/packages/lean-bench','status','--porcelain']).read_text().strip():
            raise RuntimeError('lean-bench checkout is dirty')
        run(['lake','build','hexrealclosure_bench','hexrealclosure_phase4'],timeout=3600)
        for name in ['hexrealclosure_bench','hexrealclosure_phase4']:
            snapshot = destination/name
            shutil.copy2(ROOT/'.lake/build/bin'/name,snapshot)
            record[name+'_sha256'] = digest(snapshot)
        record['oracle_version'] = run([oracle_python,'-c',
            'import flint; print(flint.__version__,flint.__FLINT_VERSION__)']).read_text().strip()
        if record['oracle_version'] != '0.9.0 3.6.0':
            raise RuntimeError('measurement requires pinned python-flint/FLINT versions')
        cpu,lease = cpu_lease()
        os.sched_setaffinity(0,{cpu})
        record.update(cpu=cpu,affinity=sorted(os.sched_getaffinity(0)),load=list(os.getloadavg()))
        fixtures = {json.loads(line)['degree']:line+'\n' for line in
                    (ROOT/'conformance-fixtures/HexRealClosure/metitarski-scaling.jsonl').read_text().splitlines()}
        record['functional'] = []
        for degree in DEGREES:
            path = run([destination/'hexrealclosure_phase4','metitarski','scaling',degree])
            if path.read_text() != fixtures[degree]:
                raise RuntimeError('snapshot functional output differs from committed fixture')
            bench_path = run([destination/'hexrealclosure_bench','meti-input',degree])
            measured = json.loads(bench_path.read_text())
            functional = json.loads(path.read_text())
            if any(measured.get(key) != functional[key] for key in
                   ['degree','head','first_coefficients','first']):
                raise RuntimeError('measured input differs from independently checked fixture')
            checked = run([oracle_python,'scripts/oracle/real_closure_metitarski_scaling.py',path])
            record['functional'].append(dict(degree=degree,fixture=path.name,measured_input=bench_path.name,oracle=checked.name))
        if run(['git','rev-parse','HEAD']).read_text().strip()!=record['commit'] or run(['git','status','--porcelain']).read_text().strip():
            raise RuntimeError('source changed before measurement')
        record['status'] = 'measuring'
        save()
        run([destination/'hexrealclosure_bench','run',FUNCTION,'--outer-trials','6',
             '--target-inner-nanos','500000000','--signal-floor-multiplier','1',
             '--export-file',destination/'measurements.json'],timeout=3600,acceptable=(0,2))
        record['status'] = 'completed'
        if run(['git','rev-parse','HEAD']).read_text().strip()!=record['commit'] or run(['git','status','--porcelain']).read_text().strip():
            raise RuntimeError('source changed during measurement')
    except BaseException as error:
        record.update(status='failed',error=str(error))
        raise
    finally:
        record['ended_utc'] = datetime.now(timezone.utc).isoformat()
        record['artifacts'] = {str(p.relative_to(destination)):digest(p)
                               for p in destination.rglob('*') if p.is_file() and p!=manifest}
        save()
        if lease is not None: lease.close()


if __name__ == '__main__':
    main()
