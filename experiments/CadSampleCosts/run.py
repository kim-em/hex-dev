#!/usr/bin/env python3
"""Fixed four-round, trial-major manual CAD sample experiment.

Run after lake build CadSampleCostsExperiment cad_sample_costs.
Outputs are append-only; each invocation requires a new output directory.
The 30 s runtime/solver and 120 s proof limits are operational cutoffs.
No completed sample is removed, no host-load condition triggers a retry.
"""
import argparse
import datetime
import fcntl
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREFIX = 'CadSampleCosts'
CASES = [('nlsat', 'Nlsat'), ('circle-parabola', 'CircleParabola'),
         ('circles', 'Circles'), ('kahan', 'Kahan'), ('sphere', 'Sphere'),
         ('tower4', 'Tower4'), ('tower8', 'Tower8')]
PROOFS = CASES + [('circle-parabola-zero', 'Vanishing')]


def capture(cmd):
    return subprocess.check_output(cmd, cwd=ROOT, text=True).strip()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def host():
    return {'load': os.getloadavg(), 'stat': Path('/proc/stat').read_text(),
            'process_count': len(capture(['ps', '-e', '-o', 'pid=']).splitlines())}


def lease_cpu():
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            os.sched_setaffinity(0, {cpu})
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError('all CPU leases held; no quiet-core waiting')


def clean(module):
    relative = Path(*module.split('.'))
    for directory in (ROOT/'.lake/build/lib/lean', ROOT/'.lake/build/ir'):
        prefix = directory/relative
        for path in prefix.parent.glob(prefix.name+'.*'):
            if path.is_file():
                path.unlink()


def timed(command, timeout, cwd, log):
    load = os.getloadavg()
    start = time.perf_counter_ns()
    with log.open('wb') as out:
        child = subprocess.Popen(command, cwd=cwd, stdout=out, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        expired = False
        try:
            code = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            expired = True
            os.killpg(child.pid, signal.SIGKILL)
            code = child.wait()
    elapsed = time.perf_counter_ns()-start
    text = log.read_text(errors='replace')
    with gzip.open(str(log)+'.gz', 'wb') as out:
        out.write(log.read_bytes())
    log.unlink()
    return {'command': command, 'timeout_s': timeout, 'timed_out': expired,
            'exit_code': code, 'wall_ns': elapsed, 'load_before': load,
            'load_after': os.getloadavg(), 'log': log.name+'.gz'}, text


def parse_trace(text):
    explanations, learned = [], []
    current = None
    for line in text.splitlines():
        if line.startswith('CAD_BEGIN '):
            if current is not None:
                raise ValueError('nested explanation')
            current = {'core_literals': int(line.split()[1]), 'projection_factors': {}}
        elif line.startswith('CAD_PROJ '):
            if current is None:
                raise ValueError('projection outside explanation')
            _, degree, poly = line.split(' ', 2)
            current['projection_factors'][poly] = int(degree)
        elif line.startswith('CAD_END '):
            if current is None:
                raise ValueError('end without explanation')
            current['conclusion_literals'] = int(line.split()[1])
            current['projection_count'] = len(current['projection_factors'])
            explanations.append(current)
            current = None
        elif line.startswith('CAD_LEARNED '):
            _, identifier, size = line.split()
            learned.append({'id': int(identifier), 'literals': int(size)})
    if current is not None:
        raise ValueError('incomplete explanation')
    return {'explanations': explanations, 'learned_clauses': learned}


def validate_axioms(output):
    """Check every expected theorem in an untimed, retained validation build."""
    result = subprocess.run(['lake', 'build', '+CadSampleCosts.Validate:olean'],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    with gzip.open(output/'validation.log.gz', 'wt') as out:
        out.write(result.stdout)
    if result.returncode:
        raise RuntimeError('untimed validation build failed; see validation.log.gz')
    found = dict(re.findall(r"'(CadSampleCosts\..*?)' depends on axioms: \[([^]]*)\]", result.stdout))
    expected = set(json.loads((HERE/'axiom-names.json').read_text()))
    if not expected.issubset(found):
        raise RuntimeError(f'missing axiom reports: {expected - found.keys()}')
    for name in expected:
        if set(found[name].split(', ')) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'unexpected axioms: {name}: {found[name]}')
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('--z3', type=Path, required=True)
    args = parser.parse_args()
    if capture(['git', 'diff', '--name-only']) or capture(['git', 'diff', '--cached', '--name-only']):
        raise RuntimeError('commit experimental sources before measuring')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    checked = validate_axioms(output)
    (output/'kernel-inputs.json').write_bytes((HERE/'kernel-inputs.json').read_bytes())
    cpu, lease = lease_cpu()
    os.environ['LEAN_NUM_THREADS'] = '1'
    meta = {'collected_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'checked_theorems': checked, 'commit': capture(['git', 'rev-parse', 'HEAD']), 'tracked_dirty': False,
            'cpu': cpu, 'rounds': 4, 'schedule': 'trial-major; adjacent Literal/Replay AB/BA',
            'toolchain': (ROOT/'lean-toolchain').read_text().strip(),
            'platform': platform.uname()._asdict(), 'cpuinfo': Path('/proc/cpuinfo').read_text().split('\n\n')[0],
            'z3_version': subprocess.check_output([str(args.z3), '-version'], cwd=output, text=True).strip(), 'z3_sha256': digest(args.z3),
            'sources': {str(p.relative_to(ROOT)): digest(p) for p in HERE.rglob('*')
                        if p.is_file() and p.suffix in {'.lean', '.py', '.smt2', '.patch', '.json'}
                        and '__pycache__' not in p.parts},
            'host_before': host()}
    (output/'.z3-trace').unlink(missing_ok=True)
    (output/'meta.json').write_text(json.dumps(meta, indent=2)+'\n')
    with (output/'runs.jsonl').open('x') as stream:
        def record(row):
            stream.write(json.dumps(row)+'\n')
            stream.flush()
            print(row['kind'], row['round'], row['example'], row.get('arm', ''),
                  'timeout' if row.get('timed_out') else row.get('exit_code'), flush=True)
        for trial in range(4):
            for name, case in CASES:
                row, text = timed([str(ROOT/'.lake/build/bin/cad_sample_costs'), name], 30,
                                  ROOT, output/f'runtime-{trial}-{name}.log')
                row.update(kind='runtime', round=trial, example=name)
                try:
                    row['stages'] = [json.loads(line) for line in text.splitlines() if line.startswith('{')]
                except ValueError as error:
                    row['parse_error'] = str(error)
                record(row)
            for name, case in PROOFS:
                for arm in (['Literal', 'Replay'] if trial % 2 == 0 else ['Replay', 'Literal']):
                    module = f'{PREFIX}.{case}.{arm}'
                    clean(module)
                    row, text = timed(['lake', 'build', f'+{module}:olean'], 120, ROOT,
                                      output/f'proof-{trial}-{name}-{arm}.log')
                    row.update(kind='proof', round=trial, example=name, arm=arm)
                    if row['exit_code'] == 0:
                        artifact = ROOT/'.lake/build/lib/lean'/Path(*module.split('.')).with_suffix('.olean')
                        row['olean_bytes'] = artifact.stat().st_size
                    record(row)
        # Counts are deterministic fixed-seed observations, not timing comparisons.
        for name, _ in CASES:
            work = output/f'z3-{name}'
            work.mkdir()
            row, text = timed([str(args.z3), '-tr:nlsat_explain', str(HERE/'smt2'/f'{name}.smt2')],
                              30, work, output/f'solver-{name}.log')
            row.update(kind='solver', round=0, example=name)
            trace = work/'.z3-trace'
            if trace.exists():
                raw = trace.read_text()
                try:
                    row.update(parse_trace(raw))
                except ValueError as error:
                    row['parse_error'] = str(error)
                with gzip.open(output/f'trace-{name}.log.gz', 'wt') as out:
                    out.write(raw)
                trace.unlink()
            row['result'] = re.findall(r'^(sat|unsat|unknown)$', text, re.M)
            record(row)
            work.rmdir()
    meta['host_after'] = host()
    (output/'meta.json').write_text(json.dumps(meta, indent=2)+'\n')
    # Keep the lease alive through every child process.
    lease.close()


if __name__ == '__main__':
    main()
