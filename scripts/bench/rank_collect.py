#!/usr/bin/env python3
"""Snapshot completed rank_measure commands, preserving raw metadata and exports.

A separate retention manifest states exactly which commands have finished. This
can snapshot a running schedule: a flushed commands.jsonl row is its completion
boundary. Repeating collection only adds completed commands and refreshes that
manifest. Every sample in each export is retained, including failures.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    source, destination = args.source.resolve(), args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    # Ignore an incomplete final journal line if a concurrent write is in flight.
    journal = (source / 'commands.jsonl').read_bytes()
    journal = journal[:journal.rfind(b'\n') + 1]
    records = [json.loads(line) for line in journal.splitlines()]
    names = ['metadata.json']
    patch = (source / 'source.patch').read_bytes()
    patch_name = 'source.patch.gz' if patch else 'source.patch'
    for optional in ('completion.json', 'handoff.json'):
        if (source / optional).exists():
            names.append(optional)
    for row in records:
        names.extend(row['label'] + suffix for suffix in ('.json', '.txt')
                     if (source / (row['label'] + suffix)).exists())
    retained = []
    for name in names:
        if name.endswith('.txt'):
            compressed = name + '.gz'
            (destination / compressed).write_bytes(gzip.compress((source / name).read_bytes(), mtime=0))
            if (destination / name).exists():
                (destination / name).unlink()
            retained.append(compressed)
        else:
            shutil.copy2(source / name, destination / name)
            retained.append(name)
    names = retained
    (destination / patch_name).write_bytes(gzip.compress(patch, mtime=0) if patch else patch)
    other_patch = destination / ('source.patch' if patch else 'source.patch.gz')
    if other_patch.exists():
        other_patch.unlink()
    names.append(patch_name)
    (destination / 'commands.jsonl').write_bytes(journal)
    (destination / 'retention.json').write_text(json.dumps({
        'source_directory': str(source),
        'source_patch_sha256': hashlib.sha256(patch).hexdigest(),
        'completed_commands': [row['label'] for row in records],
        'sha256': {name: hashlib.sha256((destination / name).read_bytes()).hexdigest()
                   for name in names + ['commands.jsonl']},
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
