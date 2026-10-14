"""Normalize all three raw OrderedFn capture files into their committed layout."""
import argparse
import json
from pathlib import Path


def normalized(directory):
    rows = json.loads((directory / 'declaration-use.json').read_text())
    rows.sort(key=lambda row: (row['module'], row['name']))
    for row in rows:
        row['users'].sort()
        row['axioms'].sort()
    fields = json.loads((directory / 'structure-fields.json').read_text())
    fields.sort(key=lambda field: (field['structure'], field['field']))
    imports = json.loads((directory / 'audit-imports.json').read_text())
    return {'declaration-use.json': rows, 'structure-fields.json': fields,
            'audit-imports.json': imports}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, data in normalized(args.directory).items():
        content = json.dumps(data, indent=2, sort_keys=True) + '\n'
        if args.check:
            if (args.directory / name).read_text() != content:
                raise ValueError('normalized artifact differs: ' + name)
        else:
            (args.directory / name).write_text(content)


if __name__ == '__main__':
    main()
