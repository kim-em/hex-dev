#!/usr/bin/env python3
"""Capture operation-only scalar and reduced-query profiles with perf and the samply filter.

Retain raw profiles locally; commit only manifests, diagnostics, and summaries.
Each invocation leases an available measurement CPU without testing its load.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

sys.path.insert(0, str(Path.cwd()))
from scripts.bench.cpu_lease import cpu_lease

ROOT = Path.cwd()
CASES = {
    'reduced-query': ('hexsturm_bench', 'Hex.SturmBench.runReducedRational', 262144, 1_000_000_000),
    'scalar-sqrt': ('hexrealalgebraic_bench', 'Hex.RealAlgebraicScaling.runSqrt4', 0, 1_000_000_000),
}



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=CASES, required=True)
    parser.add_argument('--raw', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--profiler-root', type=Path, required=True)
    parser.add_argument('--target-nanos', type=int)
    args = parser.parse_args()
    os.chdir(ROOT)
    status = subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True)
    if status:
        raise SystemExit('Profile capture requires a clean source checkout before output creation')
    args.raw.mkdir(parents=True, exist_ok=False)
    args.output.mkdir(parents=True, exist_ok=True)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    exe_name, name, param, duration = CASES[args.family]
    exe = ROOT / '.lake/build/bin' / exe_name
    record = dict(family=args.family, function=name,
                  parameter=param, cpu=cpu, load=os.getloadavg(), host=platform.node(),
                  platform=platform.platform(), raw=str(args.raw), commands=[],
                  executable_sha256=hashlib.sha256(exe.read_bytes()).hexdigest(),
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  cpu_model=next((line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), 'unknown'),
                  purpose='Required representative attribution for the remainder-only query path and unexpected canonical scalar square-root cost. Not a timing sweep or phase admission.')
    def run(command):
        result = subprocess.run(list(map(str, command)), capture_output=True, text=True)
        index = len(record['commands'])
        (args.raw / f'{index}.stdout').write_text(result.stdout)
        (args.raw / f'{index}.stderr').write_text(result.stderr)
        record['commands'].append(dict(argv=list(map(str, command)), exit_code=result.returncode))
        result.check_returncode()
        return result.stdout
    try:
        record['commit'] = run(['git', 'rev-parse', 'HEAD']).strip()
        record['dirty'] = bool(run(['git', 'status', '--porcelain']))
        record['lean_bench_commit'] = run(['git', '-C', ROOT / '.lake/packages/lean-bench', 'rev-parse', 'HEAD']).strip()
        record['lake_version'] = run(['lake', '--version']).strip()
        record['computational_source_sha256'] = {}
        for relative in ['bench/HexRealAlgebraic/Bench.lean', 'bench/HexSturm/Bench.lean', 'HexSturm/Reduced.lean', 'HexPoly/Euclid/DivGcd.lean', 'HexRealAlgebraic/Basic.lean', 'HexRealAlgebraic/Roots.lean', 'HexNumberField/Roots.lean', 'HexNumberField/Convert.lean', 'HexArith/Nat/Sqrt.lean']:
            source = ROOT / relative
            record['computational_source_sha256'][relative] = hashlib.sha256(source.read_bytes()).hexdigest()
            (args.raw / (relative.replace('/', '-') + '.txt')).write_bytes(source.read_bytes())
        record['profiler_commit'] = run(['git', '-C', args.profiler_root, 'rev-parse', 'HEAD']).strip()
        record['profiler_remote'] = run(['git', '-C', args.profiler_root,
                                         'config', '--get', 'remote.origin.url']).strip()
        record['samply_version'] = run(['samply', '--version']).strip()
        record['perf_version'] = run(['perf', '--version']).strip()
        anchor = args.raw / 'spawn-anchor.json'
        anchor.write_text(json.dumps(dict(wall_ns_at_spawn=time.time_ns(),
                                         mono_ns_at_spawn=time.monotonic_ns())))
        run(['perf', 'record', '--clockid', 'mono', '-e', 'cycles:u', '-F', '999',
             '--call-graph', 'dwarf', '-o', args.raw / 'perf.data', '--', 'env',
             f'LEAN_BENCH_TIMED_REGIONS_SIDECAR={args.raw}/timed-%p.jsonl',
             str(exe), 'profile', record['function'], '--param', param,
             '--target-inner-nanos', args.target_nanos or duration,
             '--profiler', 'env'])
        run(['samply', 'import', '--save-only', '--no-open', '--unstable-presymbolicate',
             '-o', args.raw / 'samply.json.gz', args.raw / 'perf.data'])
        samples = run(['perf', 'script', '--ns', '-F', 'pid,tid,time,event',
                       '-i', args.raw / 'perf.data'])
        (args.raw / 'perf-samples.txt').write_text(samples)
        run([sys.executable, 'scripts/profile/normalize_perf.py',
             '--profile', args.raw / 'samply.json.gz', '--perf-script', args.raw / 'perf-samples.txt',
             '--spawn-anchor', anchor, '--output', args.raw / 'normalized.json.gz'])
        sidecars = list(args.raw.glob('timed-*.jsonl'))
        if len(sidecars) != 1:
            raise RuntimeError('expected one timed-region sidecar')
        regions = [json.loads(line) for line in sidecars[0].read_text().splitlines()]
        record['timed_duration_ns'] = sum(r['mono_t1_ns'] - r['mono_t0_ns']
            for r in regions if r.get('kind') == 'region' and r.get('label') == 'kernel')
        run([sys.executable, args.profiler_root / 'scripts/filter_samply.py',
             '--samply-json', args.raw / 'normalized.json.gz', '--sidecar', sidecars[0],
             '--spawn-anchor', anchor, '--out', args.raw / 'filtered.json.gz',
             '--diagnostics', args.raw / 'diagnostics.json', '--label-filter', 'kernel'])
        run([sys.executable, 'scripts/profile/elf_symbols.py', args.raw / 'filtered.json.gz',
             '--output', args.raw / 'symbols.json'])
        diagnostics = json.loads((args.raw / 'diagnostics.json').read_text())
        run([sys.executable, 'scripts/profile/summarize_profile.py', args.raw / 'filtered.json.gz',
             '--symbols', args.raw / 'symbols.json', '--diagnostics', args.raw / 'diagnostics.json',
             '--thread', diagnostics['bench_thread_name'], '--top', 20,
             '--output', args.output / f'{args.family}.summary.json'])
        record['status'] = 'profiled'
    except BaseException as error:
        record.update(status='failed', error=str(error))
        raise
    finally:
        diagnostic = args.raw / 'diagnostics.json'
        if diagnostic.exists():
            record['diagnostics'] = json.loads(diagnostic.read_text())
        record['artifacts'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in args.raw.iterdir() if p.is_file()}
        (args.output / f'{args.family}.manifest.json').write_text(json.dumps(record, indent=2) + '\n')
        lease.close()


if __name__ == '__main__':
    main()
