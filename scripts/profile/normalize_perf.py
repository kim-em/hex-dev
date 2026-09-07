#!/usr/bin/env python3
"""Restore CLOCK_MONOTONIC times in samply-imported perf profiles.

Samply 0.13.1 imports perf samples relative to the first sample but sets
meta.startTime from the file mtime. Use the raw perf sample timestamps to
recover the offset, requiring exact agreement of the entire sample sequence.
No benchmark boundaries or timing verdicts participate in this conversion.
"""
import argparse
from decimal import Decimal
import gzip
import json
from pathlib import Path


def normalize(profile, perf_script):
    raw = sorted(int(Decimal(line.split()[1].rstrip(':')) * 10**9)
                 for line in perf_script.splitlines() if line.strip())
    relative = sorted(round(value * 10**6) for thread in profile['threads']
                      for value in thread['samples']['time'])
    if not raw or len(raw) != len(relative):
        raise ValueError('raw and imported sample counts differ or are empty')
    origin = raw[0] - relative[0]
    residual = max(abs(a - b - origin) for a, b in zip(raw, relative))
    if residual > 1:
        raise ValueError(f'raw/imported sample timestamps disagree by {residual} ns')
    for thread in profile['threads']:
        thread['samples']['time'] = [value + origin / 10**6
                                    for value in thread['samples']['time']]
    evidence = dict(sample_count=len(raw), origin_ns=origin, residual_ns=residual,
                    method='all raw perf timestamps equal imported timestamps plus one offset')
    profile['meta']['perf_clock_normalization'] = evidence
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', required=True, type=Path)
    parser.add_argument('--perf-script', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    with gzip.open(args.profile, 'rt') as source:
        profile = json.load(source)
    evidence = normalize(profile, args.perf_script.read_text())
    with gzip.open(args.output, 'wt') as target:
        json.dump(profile, target)
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
