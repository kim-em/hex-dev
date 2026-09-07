#!/usr/bin/env python3
"""Export ELF symbol intervals used by a saved profile for offline summaries."""
import argparse
import bisect
import gzip
import hashlib
import json
from pathlib import Path
import subprocess


def parse_symbols(text):
    entries = {}
    for line in text.splitlines():
        fields = line.split()
        if len(fields) == 4 and fields[2] in ('t', 'T', 'w', 'W'):
            start, size = int(fields[0], 16), int(fields[1], 16)
            if size > 0:
                entries[start] = (size, fields[3])
    return entries


def resolve(entries, starts, address):
    position = bisect.bisect_right(starts, address) - 1
    if position < 0:
        return None
    start = starts[position]
    size, name = entries[start]
    return (start, size, name) if address < start + size else None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    with gzip.open(args.profile, 'rt') as source:
        profile = json.load(source)
    addresses = {}
    for thread in profile['threads']:
        frames, funcs, resources = thread['frameTable'], thread['funcTable'], thread['resourceTable']
        for i, address in enumerate(frames['address']):
            resource = funcs['resource'][frames['func'][i]]
            if resource < 0 or address < 0:
                continue
            lib = resources['lib'][resource]
            if lib is not None:
                addresses.setdefault(lib, set()).add(address)
    strings, data, provenance = [], [], []
    for index, used in addresses.items():
        lib = profile['libs'][index]
        path = Path(lib['path'])
        if not path.is_file():
            provenance.append(dict(path=str(path), status="missing",
                resolved_addresses=0, unresolved_addresses=len(used)))
            data.append(dict(debug_name=lib["debugName"], symbol_table=[]))
            continue
        entries = {}
        for flags in (['-S', '-n', '--defined-only'], ['-D', '-S', '-n', '--defined-only']):
            command = ['nm', *flags, str(path)]
            proc = subprocess.run(command, capture_output=True, text=True, check=True)
            provenance.append(dict(command=command, stderr=proc.stderr,
                binary_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            entries.update(parse_symbols(proc.stdout))
        starts = sorted(entries)
        table = {}
        unresolved = 0
        for address in used:
            symbol = resolve(entries, starts, address)
            if symbol is None:
                unresolved += 1
            else:
                start, size, name = symbol
                table[start] = (size, name)
        symbols = []
        for rva, (size, name) in sorted(table.items()):
            symbols.append(dict(rva=rva, size=size, symbol=len(strings)))
            strings.append(name)
        provenance.append(dict(path=str(path), status="symbolized",
            resolved_addresses=len(used) - unresolved, unresolved_addresses=unresolved))
        data.append(dict(debug_name=lib['debugName'], symbol_table=symbols))
    args.output.write_text(json.dumps(dict(string_table=strings, data=data,
        provenance=provenance), indent=2) + '\n')


if __name__ == '__main__':
    main()
