#!/usr/bin/env python3
"""Fresh-module paired comparisons with the scalar study and frozen old frontend.

Build both checkouts' imports first. Every trial alternates AB/BA order.
A timed-out arm/dimension is retained and censored; its later trials are skipped.
"""
import argparse
import fcntl
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import signal
import statistics
import subprocess
import time


def kernel_seconds(log):
    units = {'s': 1, 'ms': 1e-3, 'μs': 1e-6, 'us': 1e-6, 'ns': 1e-9}
    matches = re.findall(r'\btype checking ([0-9.]+)(ms|μs|us|ns|s)\b', log)
    return sum(float(x) * units[u] for x, u in matches) if matches else None


def summarize(report):
    """Summarize complete adjacent pairs; never assign a kernel time to a timeout."""
    rows = []
    for n in report['plan']['dimensions']:
        for reference in ['Quoted', 'Original']:
            pairs = []
            for trial in range(report['plan']['paired_trials']):
                samples = [s for s in report['samples'] if s['pair'] == f'{trial}-{n}-{reference}']
                if len(samples) != 2 or any(s['exit'] != 0 for s in samples):
                    continue
                packed = next(s for s in samples if s['arm'] == 'Packed')
                ref = next(s for s in samples if s['arm'] == reference)
                pairs.append((packed['kernel_s'], ref['kernel_s']))
            if pairs:
                rows.append({'n': n, 'reference': reference, 'pairs': len(pairs),
                    'packed_s': statistics.median(p for p, _ in pairs),
                    'reference_s': statistics.median(r for _, r in pairs),
                    'speedup': statistics.median(r / p for p, r in pairs),
                    'packed_range_s': [min(p for p, _ in pairs), max(p for p, _ in pairs)]})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, nargs='?')
    parser.add_argument('--summarize', type=Path, help='Print paired medians from an existing report')
    parser.add_argument('--baseline-root', type=Path)
    args = parser.parse_args()
    if args.summarize:
        print(json.dumps(summarize(json.loads(args.summarize.read_text())), indent=2))
        return
    if args.output is None or args.baseline_root is None:
        parser.error('output and --baseline-root are required for measurement')
    root = Path(__file__).resolve().parents[3]
    baseline = args.baseline_root.resolve()
    plan = json.loads((Path(__file__).with_name('packed-plan.json')).read_text())
    baseline_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=baseline, text=True).strip()
    if baseline_commit != plan['baseline_commit']:
        raise ValueError('baseline checkout does not match the preregistered commit')
    args.output.mkdir(parents=True, exist_ok=False)
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f'/tmp/hex-bench-cpu-{cpu}.lock', 'a')
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            lease.close()
    else:
        raise RuntimeError('all CPU leases held')
    os.sched_setaffinity(0, {cpu})
    os.environ['LEAN_NUM_THREADS'] = '1'
    report = {'plan': plan, 'host': os.uname().nodename, 'cpu': cpu,
              'initial_load': os.getloadavg(), 'samples': [], 'skipped': [], 'source_sha256': {},
              'commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
              'dirty_state': subprocess.check_output(['git', 'status', '--porcelain'], cwd=root, text=True),
              'toolchain': (root / 'lean-toolchain').read_text().strip(), 'os': platform.platform(),
              'command': ['lake', 'build', 'HexCharPolyMathlib.ProofProbe.Dense{n}{arm}:olean'],
              'cleanup': 'Remove measured module artifacts; kill process group on timeout.',
              'release_quality': False,
              'verdict': 'Host-specific diagnostic comparison; no release-quality verdict.'}
    paths = ['lakefile.lean', 'HexCharPoly/Kernel.lean', 'HexCharPoly/CharPolyElab.lean',
             'HexCharPolyMathlib/Kernel.lean', 'HexCharPolyMathlib/CharPolyElab.lean',
             'bench/HexCharPolyMathlib/ProofProbe/Support.lean',
             'bench/HexCharPolyMathlib/ProofProbe/generate.py',
             'bench/HexCharPolyMathlib/ProofProbe/compare.py']
    for path in paths:
        report['source_sha256'][path] = hashlib.sha256((root / path).read_bytes()).hexdigest()
    probe = Path('bench/HexCharPolyMathlib/ProofProbe')
    for n in plan['dimensions']:
        name = f'Dense{n}Original.lean'
        (baseline / probe / name).write_bytes((root / probe / name).read_bytes())
    stopped = set()
    for censored in plan.get('censored_references', []):
        prior = json.loads((root / censored['evidence']).read_text())
        if prior['plan']['baseline_commit'] != baseline_commit or not any(
                s['n'] == censored['n'] and s['arm'] == censored['arm'] and s['exit'] == 'timeout'
                for s in prior['samples']):
            raise ValueError('censoring evidence does not match the frozen baseline timeout')
        stopped.add((censored['n'], censored['arm']))
    for trial in range(plan['paired_trials']):
        for n in plan['dimensions']:
            for reference in ['Quoted', 'Original']:
                pair = f'{trial}-{n}-{reference}'
                if (n, reference) in stopped:
                    report['skipped'].append({'pair': pair, 'reason': 'reference timed out in a retained earlier trial or sweep'})
                    continue
                arms = ['Packed', reference] if trial % 2 == 0 else [reference, 'Packed']
                for arm in arms:
                    checkout = baseline if arm == 'Original' else root
                    name = f'Dense{n}{arm}'
                    for path in (checkout / '.lake/build/lib/lean/HexCharPolyMathlib/ProofProbe').glob(name + '.*'):
                        path.unlink()
                    log_path = args.output / f'{pair}-{arm}.log'
                    start = time.monotonic()
                    with log_path.open('w') as log:
                        proc = subprocess.Popen(['lake', 'build', f'HexCharPolyMathlib.ProofProbe.{name}:olean'],
                            cwd=checkout, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                        try:
                            code = proc.wait(timeout=plan['operational_timeout_seconds'])
                        except subprocess.TimeoutExpired:
                            os.killpg(proc.pid, signal.SIGKILL)
                            proc.wait()
                            code = 'timeout'
                            stopped.add((n, arm))
                    row = {'pair': pair, 'trial': trial, 'n': n, 'arm': arm, 'exit': code,
                           'wall_s': time.monotonic() - start, 'load': os.getloadavg(),
                           'kernel_s': kernel_seconds(log_path.read_text()), 'log': log_path.name}
                    row['artifacts_bytes'] = {p.suffix: p.stat().st_size for p in
                        (checkout / '.lake/build/lib/lean/HexCharPolyMathlib/ProofProbe').glob(name + '.*')}
                    row['axioms'] = re.findall(r"'result' depends on axioms: (\[[^\]]*\])", log_path.read_text())
                    report['samples'].append(row)
                    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
                    print(json.dumps(row), flush=True)
                    if code not in [0, 'timeout'] or (arm == 'Packed' and code != 0) or (code == 0 and row['kernel_s'] is None):
                        raise RuntimeError(f'proof probe failed: {row}')
    report['paired_deltas'] = []
    for pair in dict.fromkeys(s['pair'] for s in report['samples']):
        samples = [s for s in report['samples'] if s['pair'] == pair]
        if len(samples) == 2 and all(s['exit'] == 0 for s in samples):
            packed = next(s for s in samples if s['arm'] == 'Packed')
            reference = next(s for s in samples if s['arm'] != 'Packed')
            report['paired_deltas'].append({'pair': pair,
                'kernel_reference_minus_packed_s': reference['kernel_s'] - packed['kernel_s'],
                'wall_reference_minus_packed_s': reference['wall_s'] - packed['wall_s'],
                'kernel_speedup': reference['kernel_s'] / packed['kernel_s']})
    report['summary'] = summarize(report)
    (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
