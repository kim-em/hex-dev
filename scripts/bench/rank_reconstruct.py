#!/usr/bin/env python3
"""Reconstruct archived HexRank measurement source in a new detached worktree.

Build with `lake build hexrank_bench` there. Every frozen executable named
hexrank_bench, hexrank_attribution_bench, hexrank_quotient_bench, or
hexrank_scale_bench was copied from that same Lake target. To replay a schedule,
pass the rebuilt path with rank_measure.py --bench and choose a new --out path.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / 'reports/bench-results/hex-rank-10352'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--snapshot', required=True, help='Unique archived revision prefix.')
    parser.add_argument('--destination', type=Path, required=True, help='New worktree path.')
    parser.add_argument('--run', type=Path, help='Retained run directory with a dirty source.patch[.gz].')
    args = parser.parse_args()
    manifest = json.loads((DATA / 'source/manifest.json').read_text())
    matches = [entry for entry in manifest['snapshots'] if entry['revision'].startswith(args.snapshot)]
    if len(matches) != 1:
        parser.error('snapshot must identify exactly one archived revision')
    entry = matches[0]
    packed = (DATA / 'source' / entry['patch']).read_bytes()
    patch = gzip.decompress(packed)
    if (hashlib.sha256(packed).hexdigest() != entry['sha256'] or
            hashlib.sha256(patch).hexdigest() != entry['uncompressed_sha256']):
        raise ValueError('archived source hash mismatch')
    subprocess.run(['git', 'worktree', 'add', '--detach', str(args.destination.resolve()),
                    manifest['published_base']], cwd=ROOT, check=True)
    subprocess.run(['git', 'apply'], input=patch, cwd=args.destination, check=True)
    if args.run:
        compressed = args.run / 'source.patch.gz'
        dirty = gzip.decompress(compressed.read_bytes()) if compressed.exists() else (args.run / 'source.patch').read_bytes()
        if dirty:
            subprocess.run(['git', 'apply', *['--include=' + pattern for pattern in manifest['path_scope']]],
                           input=dirty, cwd=args.destination, check=True)
        metadata = json.loads((args.run / 'metadata.json').read_text())
        for name, expected in metadata.get('source_sha256', {}).items():
            actual = hashlib.sha256((args.destination / name).read_bytes()).hexdigest()
            if actual != expected:
                raise ValueError('reconstructed source hash mismatch: ' + name)
    print('Reconstructed', entry['revision'], 'at', args.destination)


if __name__ == '__main__':
    main()
