#!/usr/bin/env python3
"""Collect operation-only GMP profiles with source hashes and timed-region samples."""
import argparse
import collections
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.kronecker_sweep import cpu_lease
from scripts.bench.fresh_module_sweep import repo_source
from scripts.ci.check_benches_mathlib_free import _ExeTarget, _parse_imports


def sources():
    target = _ExeTarget('hexkronecker_bench', 'HexKronecker.Bench', Path('bench'))
    queue, seen = ['HexKronecker.Bench'], set()
    paths = {ROOT/'lakefile.lean', ROOT/'lean-toolchain', ROOT/'lake-manifest.json', Path(__file__)}
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        seen.add(module)
        path = repo_source(module, target, ROOT/'.lake/packages')
        if path:
            paths.add(path)
            queue.extend(_parse_imports(path))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    hashes = sources()
    with tempfile.TemporaryDirectory(prefix='hex-kronecker-profile-') as directory:
        for arm in ['Tree', 'Plain', 'Packed']:
            stem = Path(directory)/arm.lower()
            os.environ['LEAN_BENCH_TIMED_REGIONS_SIDECAR'] = str(stem)+'-%p.jsonl'
            command = ['.lake/build/bin/hexkronecker_bench', 'profile', f'Hex.Kronecker.Bench.run{arm}',
                '--param', '15', '--target-inner-nanos', '2000000000', '--profiler',
                f'perf record --clockid mono -F 199 -g -o {stem}.data --']
            run = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (args.output/f'profile-{arm.lower()}.log').write_text(run.stdout)
            if run.returncode:
                raise SystemExit(run.returncode)
            raw = subprocess.check_output(['perf','script','-i',str(stem)+'.data','--no-demangle',
                '-F','time,ip,sym,dso'], text=True)
            sidecars = [json.loads(line) for p in Path(directory).glob(arm.lower()+'-*.jsonl')
                        for line in p.read_text().splitlines()]
            regions = [(r['mono_t0_ns'],r['mono_t1_ns']) for r in sidecars
                       if r['kind']=='region' and r['label']=='kernel']
            samples, outside = [], 0
            chunks = re.split(r'(?m)^(\d+\.\d+):\s*\n',raw)
            for i in range(1,len(chunks),2):
                seconds, fraction = chunks[i].split('.')
                ns = int(seconds)*10**9 + int(fraction.ljust(9,'0'))
                frames = [s.strip() for s in chunks[i+1].splitlines() if s.strip()]
                if any(a<=ns<=b for a,b in regions):
                    samples.append(dict(mono_ns=ns,frames=frames))
                else:
                    outside += 1
            counts = collections.Counter(re.sub(r'^[a-f0-9]+\s+','',s['frames'][0])
                if s['frames'] else 'unresolved' for s in samples)
            result = dict(cpu=cpu, command=command, source_hashes=hashes,
                sources_unchanged=hashes==sources(), sidecars=sidecars,
                benchmark=[json.loads(s) for s in run.stdout.splitlines() if s.startswith('{')],
                operation_samples=len(samples), outside_operation_samples=outside,
                leaf_counts=dict(counts.most_common()), samples=samples)
            (args.output/f'profile-{arm.lower()}.json').write_text(json.dumps(result,indent=2)+'\n')
            print(arm, len(samples), 'operation samples', flush=True)
    lease.close()


if __name__ == '__main__':
    main()
