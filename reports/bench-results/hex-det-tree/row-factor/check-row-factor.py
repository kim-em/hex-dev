"""Bound the existing two-case, six-pair runner; stop on its first failed build."""
import json
import sys
import time
from pathlib import Path
sys.path.insert(0, str(Path.cwd()))
from scripts.bench import det_symbolic_sweep as runner
from scripts.bench.det_bench_limits import supervise

root = Path('/tmp/issue-10320-profile')
output = root / 'row-factor-comparison.json'
observations = root / 'row-factor-observations.jsonl'
if output.exists() or observations.exists():
    raise SystemExit('refusing to overwrite retained measurements')
original = runner.sweep.build_sample

def run(deadline):
    def bounded(module, timeout, measurement_cpu=None, monitored_cpus=(),
                sample_observer=None, retain_compiler_output=False):
        def observed(name, result):
            with observations.open('a') as file:
                file.write(json.dumps(dict(module=name, result=result)) + '\n')
            if sample_observer:
                sample_observer(name, result)
        remaining = deadline - time.monotonic() - 2
        if remaining <= 0:
            raise SystemExit('three-minute comparison deadline')
        try:
            return original(module, min(timeout, 20, remaining), measurement_cpu,
                            monitored_cpus, observed, retain_compiler_output)
        except RuntimeError as exc:
            raise SystemExit(f'stopping the entire comparison after the first failure: {exc}')
    runner.sweep.build_sample = bounded
    sys.argv = ['det_symbolic_sweep.py', str(output), '--case', 'N4K1D1S1', '--case', 'N4K2D2S4']
    runner.main()

raise SystemExit(supervise(run, 180, root / 'row-factor-comparison.status.json'))
