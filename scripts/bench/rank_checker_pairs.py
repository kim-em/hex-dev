#!/usr/bin/env python3
"""Adjacent AB/BA LeanBench arms for the quotient checker investigation.

`context` compares cached checking with modular finish plus its fresh check.
`implementation` compares two frozen executables on the identical checker.
Six blocks, one automatically selected CPU, all observations retained. This
orchestrates the existing inner harness; it supplies no new timing loop or
complexity verdict. The single-rung observations diagnose constants only.
"""
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
from scripts.bench.rank_measure import output_errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('context', 'implementation'))
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--after', type=Path)
    parser.add_argument('--param', type=int, default=1024)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if args.param < 4 or args.param % 4:
        parser.error('parameter must be a positive multiple of four')
    if (args.mode == 'implementation') != (args.after is not None):
        parser.error('--after is required only for implementation comparisons')
    before = args.before.resolve()
    after = args.after.resolve() if args.after else before
    provenance = {}
    for binary in {before, after}:
        record = json.loads(binary.with_suffix('.source.json').read_text())
        if record['binary_sha256'] != hashlib.sha256(binary.read_bytes()).hexdigest():
            parser.error('frozen binary differs from its source record: ' + str(binary))
        provenance[str(binary)] = record
    prefix = 'Hex.RankBench.Quotient.'
    arms = [('check', before, prefix + 'checkFull'),
            ('finish', before, prefix + 'finishFull')] if args.mode == 'context' else [
                ('before', before, prefix + 'checkFull'),
                ('after', after, prefix + 'checkFull')]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    cpu = pick()
    os.sched_setaffinity(0, {cpu})
    schedule = []
    for block in range(6):
        for arm, binary, case in arms if block % 2 == 0 else reversed(arms):
            label = f'{block}-{arm}'
            schedule.append((label, [str(binary), 'run', case,
                '--param-floor', str(args.param), '--param-ceiling', str(args.param),
                '--param-schedule', 'doubling', '--outer-trials', '1',
                '--warmup-fraction', '0', '--target-inner-nanos', '2000000000',
                '--export-file', str(out / (label + '.json'))]))
    metadata = {
        'revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        'command': sys.argv, 'cwd': str(ROOT), 'schedule': schedule,
        'binary_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in {before, after}},
        'binary_provenance': provenance,
        'platform': platform.platform(), 'hostname': platform.node(),
        'cpu_description': subprocess.check_output(['lscpu'], text=True),
        'cpu': cpu, 'affinity': sorted(os.sched_getaffinity(0)),
        'load_at_start': os.getloadavg(),
        'toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'harness_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'],
            cwd=ROOT / '.lake/packages/lean-bench', text=True).strip(),
    }
    (out / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    (out / 'source.patch').write_bytes(subprocess.check_output(['git', 'diff', 'HEAD']))
    failures = []
    with (out / 'commands.jsonl').open('w') as history:
        for label, command in schedule:
            started = time.time()
            with (out / (label + '.txt')).open('w') as log:
                result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
            errors = output_errors(out / (label + '.json'))
            record = {'label': label, 'command': command, 'exit_code': result.returncode,
                      'output_errors': errors, 'started_epoch': started,
                      'wall_seconds': time.time() - started, 'load_after': os.getloadavg()}
            history.write(json.dumps(record) + '\n')
            history.flush()
            print(label, result.returncode, errors, flush=True)
            if result.returncode or errors:
                failures.append(label)
    (out / 'completion.json').write_text(json.dumps({
        'completed': len(schedule), 'scheduled': len(schedule), 'failures': failures,
        'load_at_end': os.getloadavg()}, indent=2) + '\n')
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
