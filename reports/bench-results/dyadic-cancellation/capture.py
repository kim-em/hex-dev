#!/usr/bin/env python3
"""Retain fractional-Horner scaling and adjacent before/after comparisons.

Build both arms with identical benchmark sources and toolchain. The before
arm uses the supplied Basic.lean snapshot; the after arm uses the checkout.
All measurements run sequentially on one leased CPU. No samples are filtered.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.det_symbolic_sweep import cpu_lease


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before-roots', type=Path, required=True)
    parser.add_argument('--before-sturm', type=Path, required=True)
    parser.add_argument('--before-source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    binaries = {
        'roots': {'A': args.before_roots.resolve(), 'B': ROOT / '.lake/build/bin/hexrealroots_bench'},
        'sturm': {'A': args.before_sturm.resolve(), 'B': ROOT / '.lake/build/bin/hexsturm_bench'},
    }
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    meta = dict(cpu=cpu, host=os.uname().nodename, start=now(), load_start=os.getloadavg(),
                git_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
                git_status=subprocess.check_output(['git', 'status', '--short'], cwd=ROOT, text=True),
                binaries={k: {a: dict(path=str(p), sha256=sha(p)) for a, p in arms.items()}
                          for k, arms in binaries.items()}, sources={}, commands=[])
    sources = {'before.Basic.lean': args.before_source, 'after.Basic.lean': ROOT / 'HexRealRoots/Basic.lean',
               'RealRoots.Bench.lean': ROOT / 'bench/HexRealRoots/Bench.lean',
               'Sturm.Bench.lean': ROOT / 'bench/HexSturm/Bench.lean',
               'derivation.md': ROOT / 'reports/sturm-bit-cost-models.md',
               'capture.py': Path(__file__), 'lean-toolchain': ROOT / 'lean-toolchain'}
    for name, source in sources.items():
        (out / name).write_bytes(source.read_bytes())
        meta['sources'][name] = sha(source)

    def save():
        (out / 'metadata.json').write_text(json.dumps(meta, indent=2) + '\n')

    def run(argv, name, timeout):
        record = dict(argv=list(map(str, argv)), output=name, start=now(), load_start=os.getloadavg())
        meta['commands'].append(record)
        save()
        print(name, flush=True)
        with (out / name).open('w') as log:
            try:
                result = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
                record['exit_code'] = result.returncode
            except subprocess.TimeoutExpired:
                record['timeout'] = True
                raise
            finally:
                record.update(end=now(), load_end=os.getloadavg())
                save()
        result.check_returncode()

    try:
        run([binaries['roots']['B'], 'run', 'Hex.RealRootsBench.runCancellation',
             '--export-file', out / 'scaling.json'], 'scaling.log', 3600)
        summaries = []
        for kind, name, degree, cap in [('roots', 'Hex.RealRootsBench.runCancellation', 32768, 120),
                                       ('roots', 'Hex.RealRootsBench.runCancellation', 65536, 120),
                                       ('sturm', 'Hex.SturmBench.runReplay', 1024, 1800)]:
            pairs = []
            for block in range(4):
                rows = {}
                for arm in ('AB' if block % 2 == 0 else 'BA'):
                    filename = f'{kind}-{degree}-{block}-{arm}.jsonl'
                    run([binaries[kind][arm], '_child', '--bench', name, '--param', str(degree),
                         '--target-nanos', '100000000', '--cache-mode', 'warm'], filename, cap)
                    rows[arm] = json.loads((out / filename).read_text())
                    if rows[arm]['status'] != 'ok':
                        raise RuntimeError(f'failed child retained in {filename}')
                if rows['A']['result_hash'] != rows['B']['result_hash']:
                    raise RuntimeError('result hashes differ')
                pairs.append(rows['A']['per_call_nanos'] / rows['B']['per_call_nanos'])
            summaries.append(dict(function=name, degree=degree, before_over_after=pairs,
                                  median_ratio=statistics.median(pairs)))
        (out / 'pairs.json').write_text(json.dumps(summaries, indent=2) + '\n')
    finally:
        meta.update(end=now(), load_end=os.getloadavg())
        save()
        lease.close()


if __name__ == '__main__':
    main()
