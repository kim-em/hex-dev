#!/usr/bin/env python3
"""Capture and attribute the prepared Pollard p-1 continuation using perf/samply."""
import argparse
import gzip
import json
import os
from pathlib import Path
import shutil
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.bench import idle_core, intfactor_phase4 as collector


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--profiler-root', required=True, type=Path)
    args = parser.parse_args()
    attempt = collector.Attempt(args.output)
    directory = attempt.directory
    cpu = idle_core.pick()
    os.sched_setaffinity(0, {cpu})
    exe = collector.ROOT / '.lake/build/bin/hexprimality_bench'
    def run(command):
        return attempt.execute(list(map(str, command)), stdin=None, timeout=120, allowed=(0,))
    try:
        sources = ['HexPrimality/PMinusOne.lean', 'bench/HexPrimality/Bench.lean',
                   'scripts/profile/pminusone.py']
        attempt.record.update(cpu=cpu, load_before=os.getloadavg(),
            executable_sha256=collector.sha256(exe),
            source_sha256={p:collector.sha256(collector.ROOT/p) for p in sources},
            profiler_commit=run(['git','-C',args.profiler_root,'rev-parse','HEAD']).stdout.strip())
        anchor = directory/'spawn-anchor.json'
        anchor.write_text(json.dumps({'wall_ns_at_spawn':time.time_ns(),
                                     'mono_ns_at_spawn':time.monotonic_ns()}))
        run(['perf','record','--clockid','mono','-e','cycles:u','-F','999',
             '--call-graph','dwarf','-o',directory/'perf.data','--','env',
             f'LEAN_BENCH_TIMED_REGIONS_SIDECAR={directory}/timed-%p.jsonl',
             exe,'_child','--bench','Hex.PrimalityBench.Stage2.Bits512.runTrace',
             '--param','32749','--target-nanos','5000000000'])
        run(['samply','import','--save-only','--no-open','--unstable-presymbolicate',
             '-o',directory/'samply.json.gz',directory/'perf.data'])
        samples=run(['perf','script','--ns','-F','pid,tid,time,event','-i',directory/'perf.data']).stdout
        (directory/'perf-samples.txt').write_text(samples)
        run([sys.executable,collector.ROOT/'scripts/profile/normalize_perf.py',
             '--profile',directory/'samply.json.gz','--perf-script',directory/'perf-samples.txt',
             '--spawn-anchor',anchor,'--output',directory/'normalized.json.gz'])
        sidecars=list(directory.glob('timed-*.jsonl'))
        assert len(sidecars)==1
        run([sys.executable,args.profiler_root/'scripts/filter_samply.py',
             '--samply-json',directory/'normalized.json.gz','--sidecar',sidecars[0],
             '--spawn-anchor',anchor,'--out',directory/'filtered.json.gz',
             '--diagnostics',directory/'diagnostics.json','--label-filter','warm-loop'])
        run([sys.executable,collector.ROOT/'scripts/profile/elf_symbols.py',
             directory/'filtered.json.gz','--output',directory/'symbols.json'])
        run([sys.executable,collector.ROOT/'scripts/profile/summarize_profile.py',
             directory/'filtered.json.gz','--symbols',directory/'symbols.json',
             '--diagnostics',directory/'diagnostics.json','--thread','hexprimality_be',
             '--top','25','--output',directory/'summary.json'])
        collector.verify_sources(attempt)
        attempt.record['status']='profiled'
    except BaseException as error:
        attempt.record.update(status='failed',error=str(error))
        raise
    finally:
        raw=directory/'perf.data'
        if raw.exists():
            with raw.open('rb') as source,gzip.open(directory/'perf.data.gz','wb') as dest:
                shutil.copyfileobj(source,dest)
            raw.unlink()
        attempt.record.update(load_after=os.getloadavg(),
            artifact_sha256={p.name:collector.sha256(p) for p in directory.iterdir() if p.is_file()})
        attempt.save()

if __name__=='__main__':
    main()
