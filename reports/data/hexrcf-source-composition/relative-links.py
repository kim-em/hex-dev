from pathlib import Path
import re,subprocess
root=next(p for p in Path(__file__).resolve().parents if (p/'.git').exists())
files=subprocess.check_output(['git','diff','bc897ef78001b40cb3654bd7bfb85e7637f7101f','--name-only'],cwd=root,text=True).splitlines()
count=0;checked=0
for name in files:
 p=root/name
 if p.suffix not in ['.md','.lean'] or not p.is_file():continue
 checked+=1
 for m in re.finditer(r'\[[^\]\n]+\]\(([^)\n]+)\)',p.read_text()):
  link=m.group(1).strip().strip('<>')
  if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:',link) or link.startswith(('#','/')):continue
  target=link.split('#',1)[0]
  if not target:continue
  assert (p.parent/target).exists(),f'{name}: broken {link}'
  count+=1
print(f'Checked filesystem-relative links: {count} links across {checked} changed Lean/Markdown files')
