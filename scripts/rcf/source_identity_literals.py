#!/usr/bin/env python3
"""Render the frozen source-equation and enclosure packets without production."""
import argparse
import json
from pathlib import Path

from selected_literals import render

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / 'conformance-fixtures/HexRCF/source-identity.json'
OUTPUT = ROOT / 'conformance/HexRCF/SourceIdentityLiterals.lean'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    records = json.loads(FIXTURE.read_text())
    if len(records) != 3 or [entry[1] for entry in records] != [0, 1, -1]:
        raise ValueError('expected equation, positive and negative enclosure packets')
    source = render('SourceIdentityPackets', records).replace(
        '`conformance-fixtures/HexRCF/selected-root.json`',
        '`conformance-fixtures/HexRCF/source-identity.json`')
    if args.check:
        if OUTPUT.read_text() != source:
            raise SystemExit('source identity constructor literals are stale')
        print('Source identity constructor literals are current')
    else:
        OUTPUT.write_text(source)


if __name__ == '__main__':
    main()
