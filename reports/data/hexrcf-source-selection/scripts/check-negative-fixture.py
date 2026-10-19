#!/usr/bin/env python3
"""Check the negative-root JSON fixture against retained native Repr output."""
import argparse
import gzip
import json
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('producer_log', type=Path)
parser.add_argument('fixture', type=Path)
args = parser.parse_args()
raw = args.producer_log.read_bytes()
text = (gzip.decompress(raw) if args.producer_log.suffix == '.gz' else raw).decode()
text = text.split('info: SourceSelectionEmitter.lean:6:0: ', 1)[1]
text = text.split('\nBuild completed successfully', 1)[0]
tokens = re.findall(r'[A-Za-z_][A-Za-z0-9_.]*|-?\d+|[()]', text)
position = 0

def read():
    global position
    token = tokens[position]
    position += 1
    if token == '(':
        value = read()
        assert tokens[position] == ')'
        position += 1
        return value
    if re.fullmatch(r'-?\d+', token):
        return int(token)
    tag = token.rsplit('.', 1)[-1]
    if tag == 'nil':
        return []
    if tag in ('number', 'array'):
        return read()
    if tag == 'cons':
        head, tail = read(), read()
        return [head] + tail
    raise ValueError(token)

proposal = [read(), read()]
assert position == len(tokens)
encoded = (json.dumps(proposal, separators=(',', ':')) + '\n').encode()
assert args.fixture.read_bytes() == encoded
print('Native Repr conversion matches the negative-root JSON fixture byte for byte')
