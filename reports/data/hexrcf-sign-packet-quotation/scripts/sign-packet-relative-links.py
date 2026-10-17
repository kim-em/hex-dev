from pathlib import Path
import re
paths=['reports/hexrcf-sign-packet-quotation.md','HexManual/Chapters/HexRCF/RootQuote.lean','HexRCF/README.md']
count=0
for item in paths:
 p=Path(item)
 for match in re.finditer(r'\]\(([^)]+)\)',p.read_text()):
  target=match.group(1).split('#')[0]
  if not target or '://'in target:continue
  assert (p.parent/target).exists(),(item,target)
  count+=1
print(f'{count} relative filesystem links exist across report, manual and README; absolute URLs are outside this check.')
