#!/usr/bin/env python3
"""Run a fixed partition of a retained comparison schedule's pending commands.

Each comparison case hashes to one partition, so all of its remaining AB/BA
blocks stay on one CPU and in their declared order. This never reschedules a
completed command. The initial journal must be frozen before invoking workers.
Each worker records a fresh same-CPU protocol control and the original binary
provenance. No timing result changes the partition or schedule.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick
from scripts.bench.rank_measure import output_errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--partition', type=int, required=True)
    parser.add_argument('--partitions', type=int, default=8)
    args = parser.parse_args()
    if not 0 <= args.partition < args.partitions:
        parser.error('partition must be in [0, partitions)')
    source, out = args.source.resolve(), args.out.resolve()
    handoff = json.loads((source / 'handoff.json').read_text())
    if not handoff.get('controller_stopped'):
        raise ValueError('stop the original controller at a recorded completion boundary first')
    base = json.loads((source / 'metadata.json').read_text())
    journal = (source / 'commands.jsonl').read_bytes()
    finished = {json.loads(line)['label'] for line in journal.splitlines()}
    schedule = []
    for label, original in base['schedule']:
        case = label.split('-', 1)[1]
        partition = int.from_bytes(hashlib.sha256(case.encode()).digest()[:8], 'big') % args.partitions
        if label in finished or partition != args.partition:
            continue
        command = original.copy()
        command[command.index('--export-file') + 1] = str(out / (label + '.json'))
        schedule.append((label, command))
    bench = Path(base['schedule'][0][1][0])
    if hashlib.sha256(bench.read_bytes()).hexdigest() != base['binary_sha256']:
        raise ValueError('the original frozen executable has changed')
    out.mkdir(parents=True, exist_ok=False)
    cpu = pick()
    os.sched_setaffinity(0, {cpu})
    env = dict(os.environ, HEX_RANK_BENCH_PYTHON=base['python'])
    metadata = {'binary_provenance': str(source / 'metadata.json'),
        'binary_sha256': base['binary_sha256'], 'cwd': base['cwd'], 'python': base['python'],
        'comparator_versions': base['comparator_versions'], 'cpu': cpu,
        'affinity': sorted(os.sched_getaffinity(0)), 'load_at_start': os.getloadavg(),
        'partition': args.partition, 'partitions': args.partitions, 'schedule': schedule,
        'completed_journal_sha256': hashlib.sha256(journal).hexdigest(),
        'runner_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'command': sys.argv, 'protocol_control': 'overhead.json'}
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (out / 'source.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD'], cwd=ROOT))
    control = [str(bench), 'run', 'Hex.RankBench.runProtocolOverhead', '--export-file', str(out / 'overhead.json')]
    failures = []
    with (out / 'commands.jsonl').open('w') as history:
        for label, command in [('overhead', control), *schedule]:
            if (source / 'commands.jsonl').read_bytes() != journal:
                raise ValueError('the frozen source journal changed')
            started = time.time()
            with (out / (label + '.txt')).open('w') as log:
                result = subprocess.run(command, cwd=base['cwd'], env=env, stdout=log, stderr=subprocess.STDOUT)
            errors = output_errors(out / (label + '.json'))
            row = {'label': label, 'command': command, 'exit_code': result.returncode,
                   'output_errors': errors, 'started_epoch': started,
                   'wall_seconds': time.time() - started, 'load_after': os.getloadavg()}
            history.write(json.dumps(row) + '\n')
            history.flush()
            print(label, result.returncode, flush=True)
            if result.returncode or errors:
                failures.append(label)
    (out / 'completion.json').write_text(json.dumps({'completed': len(schedule),
        'scheduled': len(schedule), 'failures': failures}, indent=2) + '\n')
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
