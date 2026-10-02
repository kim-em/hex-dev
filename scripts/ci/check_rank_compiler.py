#!/usr/bin/env python3
"""Check the compiled public producers use the proved array reduction.

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
