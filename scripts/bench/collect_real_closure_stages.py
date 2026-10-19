"""Collect the registered fixed-stage protocol through lean-bench."""
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

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / 'scripts' / 'bench'))
from cpu_lease import cpu_lease

STAGES = ('runYun', 'runAssembly', 'runRoots', 'runNativeRoots')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    binary = REPO / '.lake/build/bin/hexrealclosure_bench'
    cpu, lease = cpu_lease()
    try:
        os.sched_setaffinity(0, {cpu})
        def git(*arguments: str) -> str:
            return subprocess.check_output(['git', *arguments], cwd=REPO, text=True).strip()
        if git('status', '--porcelain'):
            raise RuntimeError('protocol source must be committed before collection')
        metadata = {
            'source': git('rev-parse', 'HEAD'), 'host': platform.node(),
            'platform': platform.platform(), 'cpu': cpu,
            'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
            'lean_toolchain': (REPO / 'lean-toolchain').read_text().strip(),
            'lake_manifest': json.loads((REPO / 'lake-manifest.json').read_text()),
            'trial_major_order': list(STAGES), 'rounds': 6,
            'arguments': ['--repeats', '1', '--min-total-seconds', '0.2'],
            'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
            'observations': [],
        }
        manifest = destination / 'metadata.json'
        manifest.write_text(json.dumps(metadata, indent=2) + '\n')
        for trial in range(6):
            for stage in STAGES:
                name = f'{trial:02d}-{stage}'
                export = destination / f'{name}.json'
                command = [str(binary), 'run', f'Hex.RealClosure.Bench.{stage}',
                           *metadata['arguments'], '--export-file', str(export)]
                observation = {'trial': trial, 'stage': stage,
                               'load_before': list(os.getloadavg()), 'command': command}
                with (destination / f'{name}.log').open('w') as log:
                    result = subprocess.run(command, cwd=REPO, stdout=log, stderr=subprocess.STDOUT,
                                            env={**os.environ, 'LEAN_ABORT_ON_PANIC': '1'})
                observation.update(exit_code=result.returncode, load_after=list(os.getloadavg()))
                metadata['observations'].append(observation)
                manifest.write_text(json.dumps(metadata, indent=2) + '\n')
                print(f'{name}: exit {result.returncode}', flush=True)
                if result.returncode:
                    raise RuntimeError(f'failed invocation retained: {name}')
        metadata['completed_utc'] = time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())
        manifest.write_text(json.dumps(metadata, indent=2) + '\n')
    finally:
        lease.close()


if __name__ == '__main__':
    main()
