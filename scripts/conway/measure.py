#!/usr/bin/env python3
"""Measure clean Conway rebuilds, retaining dependency caches (Linux).

First build the targets to warm dependencies. Run from the repository root.
All Conway output directories and umbrella artifacts are removed before each
run; --no-cache forbids Lake restoring the removed outputs from remote cache.
GNU time reports maximum child RSS; sampled process-tree RSS also captures
simultaneous compilers. Raw verbose logs retain per-module timings.
"""
import argparse
import hashlib
import signal
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import time


def clean(prefix):
    root = Path('.lake/build')
    for path in list(root.rglob('*')):
        if path.exists() and (path.name == prefix or path.name.startswith(prefix + '.')):
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()


def rss_tree(pid):
    pending, total = [pid], 0
    while pending:
        current = pending.pop()
        try:
            status = Path(f'/proc/{current}/status').read_text()
            match = re.search(r'VmRSS:\s+(\d+)', status)
            total += int(match[1]) if match else 0
            
            for task in Path(f'/proc/{current}/task').iterdir():
                pending.extend(map(int, (task/'children').read_text().split()))
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('label')
    ap.add_argument('--runs', type=int, default=3)
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--companion', action='store_true')
    ap.add_argument('--ceiling', type=float, default=0, help='Terminate candidates exceeding this wall time; zero means no cap')
    ap.add_argument('--keep-going', action='store_true', help='Record all failed or capped candidate runs')
    args = ap.parse_args()
    prefix = 'HexGFqMathlib' if args.companion else 'HexConway'
    targets = ['HexGFqMathlib.Primitivity', 'HexGFqMathlib.Subfield'] if args.companion else ['HexConway']
    out = Path('reports/conway'); out.mkdir(exist_ok=True, parents=True)
    report = dict(machine=platform.node(), cpu=next(x.split(':',1)[1].strip() for x in Path('/proc/cpuinfo').read_text().splitlines() if x.startswith('model name')), platform=platform.platform(), toolchain=Path('lean-toolchain').read_text().strip(), threads=args.threads, targets=targets, commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(), runs=[])
    report['source_sha256'] = {str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted([*Path(prefix).rglob('*.lean'),Path(prefix+'.lean')]) if p.exists()}
    for i in range(args.runs):
        clean(prefix)
        log = out / f'{args.label}-{i+1}.log'
        timing = out / f'{args.label}-{i+1}.time'
        cmd = ['time','-v','-o',str(timing),'lake','--no-cache','-v','build',*targets]
        start, peak = time.monotonic(), 0
        with log.open('w') as f:
            proc = subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT, env={**os.environ,'LEAN_NUM_THREADS':str(args.threads)}, start_new_session=True)
            while proc.poll() is None:
                peak = max(peak,rss_tree(proc.pid)); time.sleep(.1)
                if args.ceiling and time.monotonic()-start > args.ceiling:
                    os.killpg(proc.pid,signal.SIGTERM)
                    proc.wait()
        wall = time.monotonic()-start
        sizes = {str(p):p.stat().st_size for p in Path('.lake/build').rglob('*') if p.is_file() and (prefix in p.parts or p.name.startswith(prefix+'.'))}
        rss_match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing.read_text())
        max_child_rss = int(rss_match[1]) if rss_match else None
        row = dict(max_child_rss_kib=max_child_rss, wall_seconds=wall, peak_tree_rss_kib=peak, exit_code=proc.returncode, artifact_bytes=sum(sizes.values()), artifacts=sizes, modules=re.findall(r'Built ([^\n]+)',log.read_text()), log=str(log), timing=str(timing))
        report['runs'].append(row)
        (out / f'{args.label}.json').write_text(json.dumps(report,indent=2)+'\n')
        print(f'{args.label} {i+1}: {wall:.3f}s, tree RSS {peak} KiB, exit {proc.returncode}',flush=True)
        if proc.returncode and not args.keep_going: raise SystemExit(proc.returncode)

if __name__ == '__main__': main()
