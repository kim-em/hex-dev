from pathlib import Path
import re,subprocess
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358');count=0;checked=0
for name in subprocess.check_output(['git','diff','805d2ab1135a4ffca23322665729347b77907758','--name-only'],cwd=root,text=True).splitlines():
 p=root/name
 if p.suffix not in ['.md','.lean'] or not p.is_file():continue
 checked+=1
 for match in re.finditer(r'\[[^\]\n]+\]\(([^)\n]+)\)',p.read_text()):
  link=match.group(1).strip().strip('<>')
  if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:',link) or link.startswith(('#','/')):continue
  target=link.split('#',1)[0]
  if not target:continue
  assert (p.parent/target).exists(),f'{name}: broken {link}'
  count+=1
print(f'Checked filesystem-relative links: {count} links across {checked} changed Lean/Markdown files')
