"""Check relative filesystem destinations in the changed documentation."""
from pathlib import Path
import re

repo = Path(__file__).resolve().parents[4]
count = 0
for name in ['reports/hexrcf-public-packet-quotation.md',
             'reports/hexrcf-sign-packet-quotation.md', 'HexRCF/README.md',
             'HexManual/Chapters/HexRCF/RootQuote.lean',
             'HexManual/Chapters/HexRCF/RootTableQuote.lean']:
    path = repo / name
    for match in re.finditer(r'\]\(([^)]+)\)', path.read_text()):
        target = match.group(1).split('#')[0]
        if not target or '://' in target:
            continue
        assert (path.parent / target).exists(), (name, target)
        count += 1
print(f'{count} relative filesystem destinations exist; URL/anchor validity is outside this check.')
