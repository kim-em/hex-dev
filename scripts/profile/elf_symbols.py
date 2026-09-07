#!/usr/bin/env python3
"""Export ELF symbol intervals used by a saved profile for offline summaries."""
import argparse
import bisect
import gzip
import hashlib
import json
from pathlib import Path
import subprocess


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
            continue
        entries = {}
        for flags in (['-n', '--defined-only'], ['-D', '-n', '--defined-only']):
            command = ['nm', *flags, str(path)]
            proc = subprocess.run(command, capture_output=True, text=True, check=True)
            provenance.append(dict(command=command, stderr=proc.stderr,
                binary_sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
            for line in proc.stdout.splitlines():
                fields = line.split()
                if len(fields) == 3 and fields[1] in ('t', 'T', 'w', 'W'):
                    entries[int(fields[0], 16)] = fields[2]
        starts = sorted(entries)
        table = {}
        for address in used:
            position = bisect.bisect_right(starts, address) - 1
            if position >= 0:
                rva = starts[position]
                table[rva] = entries[rva]
        symbols = []
        for rva, name in sorted(table.items()):
            symbols.append(dict(rva=rva, symbol=len(strings)))
            strings.append(name)
        data.append(dict(debug_name=lib['debugName'], symbol_table=symbols))
    args.output.write_text(json.dumps(dict(string_table=strings, data=data,
        provenance=provenance), indent=2) + '\n')


if __name__ == '__main__':
    main()
