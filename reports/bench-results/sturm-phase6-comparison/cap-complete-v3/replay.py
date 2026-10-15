#!/usr/bin/env python3
"""Verify this capture and optionally replay its native guard; never measure."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import socket
import subprocess
import tempfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--guard', type=Path, help='original hash-bound native guard')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'manifest.json').read_text())
    replays = []
    with tempfile.TemporaryDirectory(prefix='sturm-complete-replay-') as directory:
        out = Path(directory)
        for name, record in manifest['files'].items():
            require(Path(name).name == name, 'non-flat capture path')
            require(Path(record['archive']).name == record['archive'], 'non-flat archive path')
            packed = (root / record['archive']).read_bytes()
            require(digest(packed) == record['archive_sha256'], f'archive digest: {name}')
            raw = gzip.decompress(packed)
            require(len(raw) == record['bytes'] and digest(raw) == record['sha256'],
                    f'original binding: {name}')
            (out / name).write_bytes(raw)
        context = json.loads((out / 'context.json').read_text())
        require(len(context['benchmarks']) == manifest['families'] == 58,
                'expected the complete 58-family capture')
        require(context['trials'] == manifest['blocks'] == 4,
                'expected four complete blocks')
        require(context['status'] == 'completed' and context['pass'] is True,
                'capture did not complete successfully')
        if args.guard:
            guard = args.guard.resolve()
            require(digest(guard.read_bytes()) == context['guard_sha256'], 'guard digest')
            for i, name in enumerate(context['benchmarks']):
                destination = out / f'replay-{i}.json'
                exports = [str(out / f'{block}-{i}-{arm}.json')
                           for arm in ('baseline', 'candidate') for block in range(4)]
                result = subprocess.run([str(guard), str(destination), *exports],
                                        capture_output=True, text=True, check=True)
                actual = json.loads(destination.read_text())
                require(actual == json.loads((out / f'guard-{i}.json').read_text()),
                        f'native report differs: {name}')
                replays.append(dict(function=name, returncode=result.returncode, report_equal=True))
    print(json.dumps(dict(
        driver_sha256=digest(Path(__file__).read_bytes()), host=socket.gethostname(),
        archive_files=len(manifest['files']), all_archive_hashes_valid=True,
        guard_sha256=context['guard_sha256'] if args.guard else None,
        guard_replays=replays, all_reports_equal=True if args.guard else None,
        new_measurements=False), indent=2))


if __name__ == '__main__':
    main()
