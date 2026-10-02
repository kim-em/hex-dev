#!/usr/bin/env python3
"""Check rank computation uses its proved array compiler replacements.

Run after lake build hexrank_bench. A source import check would miss changes in
compiler replacement visibility, which originally let the reference reducer
survive in these entry points even though the umbrella imported ReduceImpl.
"""
from pathlib import Path
import re

source = Path('.lake/build/ir/HexRank/Produce.c').read_text()
calls = re.findall(r'=\s*\w+_rowReduceWith(Impl)?(?:___\w+)?\(', source)
if len(calls) < 3 or any(call != 'Impl' for call in calls):
    raise SystemExit('public rank producers no longer consistently call rowReduceWithImpl')
print(f'check_rank_compiler: {len(calls)} array-reduction calls, no reference calls')

source = Path('.lake/build/ir/HexRank/Polynomial.c').read_text()


def require_replacement(caller, callee):
    definition = re.search(r'^LEAN_EXPORT uint8_t \w+_' + caller + r'\([^;\n]+\)\{', source, re.M)
    if definition is None:
        raise SystemExit('cannot find compiled ' + caller + ' definition')
    body = source[definition.end():].split('\nLEAN_EXPORT ', 1)[0]
    calls = re.findall(r'=\s*\w+_' + callee + r'(Impl)?\(', body)
    if calls != ['Impl']:
        raise SystemExit('compiled ' + caller + ' no longer uses ' + callee + 'Impl')


require_replacement('checkRankPoly', 'lowerCheck')
require_replacement('rowCheck', 'dot')
print('check_rank_compiler: quotient checker compacts rows inside its timed call')
print('check_rank_compiler: exact row relations use the borrowed tail-recursive dot')
