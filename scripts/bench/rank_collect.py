#!/usr/bin/env python3
"""Snapshot completed rank_measure commands, preserving raw metadata and exports.

A separate retention manifest states exactly which commands have finished. This
can snapshot a running schedule: a flushed commands.jsonl row is its completion
boundary. Repeating collection only adds completed commands and refreshes that
manifest. Every sample in each export is retained, including failures.
"""
import argparse
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
    names = ['metadata.json', 'source.patch']
    if (source / 'completion.json').exists():
        names.append('completion.json')
    for row in records:
        names.extend(row['label'] + suffix for suffix in ('.json', '.txt')
                     if (source / (row['label'] + suffix)).exists())
    for name in names:
        shutil.copy2(source / name, destination / name)
    (destination / 'commands.jsonl').write_bytes(journal)
    (destination / 'retention.json').write_text(json.dumps({
        'source_directory': str(source),
        'completed_commands': [row['label'] for row in records],
        'sha256': {name: hashlib.sha256((destination / name).read_bytes()).hexdigest()
                   for name in names + ['commands.jsonl']},
    }, indent=2) + '\n')


if __name__ == '__main__':
    main()
