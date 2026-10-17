from pathlib import Path
import re,sys
root=Path(sys.argv[1])
paths=['reports/hexrcf-packet-quotation.md','HexManual/Chapters/HexRCF/RootTableQuote.lean','HexManual/Chapters/HexRCF/RootQuote.lean']
count=0
for item in paths:
 p=root/item
 for match in re.finditer(r'\]\(([^)]+)\)',p.read_text()):
  target=match.group(1).split('#')[0]
  if not target or '://'in target:continue
  assert(p.parent/target).exists(),(item,target)
  count+=1
print(f'{count} relative filesystem links exist across the report and manual source. Absolute web URLs are not fetched.')
manual=(root/paths[1]).read_text()
assert '](../../../reports/'not in manual,'Manual reports must link to the rendered-safe GitHub URL'
print('Manual report link uses the rendered-safe GitHub URL.')
