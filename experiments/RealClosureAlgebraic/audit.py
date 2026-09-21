#!/usr/bin/env python3
"""Check local experiment boundaries and retained measurement source identities."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
roots=[HERE, ROOT, ROOT/'.lake/packages/lean-bench', HERE/'.lake/packages/Cli']
def uncomment(source):
    out=[]
    depth=0
    i=0
    while i<len(source):
        pair=source[i:i+2]
        if pair=='/-':
            depth+=1
            i+=2
        elif depth and pair=='-/':
            depth-=1
            i+=2
        elif not depth and pair=='--':
            end=source.find('\n',i)
            i=len(source) if end<0 else end
        else:
            if not depth or source[i]=='\n': out.append(source[i])
            i+=1
    return ''.join(out)

seen={}
pending=['Bench','Check','Tests','Transfer','PolicyBench','PolicyCheck','PolicyTrace','Refinement']
while pending:
    module=pending.pop()
    assert not module.startswith(('Mathlib','HexInterval')), module
    if module in seen or module.split('.')[0] in {'Init','Std','Lean','Lake'}:
        continue
    candidates=[r/Path(*module.split('.')).with_suffix('.lean') for r in roots]
    file=next((p for p in candidates if p.exists()),None)
    assert file is not None, (module,candidates)
    seen[module]=file
    for line in uncomment(file.read_text()).splitlines():
        match=re.match(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',line)
        if match: pending.append(match[1])
meta=json.loads((HERE/'results/timing/metadata.json').read_text())
for name in ['Algebraic.lean','Bench.lean']:
    file=HERE/name
    expected=meta['hashes'][str(file.relative_to(ROOT))]
    source=file.read_bytes()
    header=b'/-\nCopyright (c) 2026 Lean FRO, LLC. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Kim Morrison\n-/\n\n'
    assert hashlib.sha256(source).hexdigest()==expected or (source.startswith(header) and
        hashlib.sha256(source[len(header):]).hexdigest()==expected), file
policy=json.loads((HERE/'results/policy/timing/metadata.json').read_text())
for name in ['Algebraic.lean','Policy.lean','PolicyBench.lean']:
    file=HERE/name
    assert hashlib.sha256(file.read_bytes()).hexdigest()==policy['hashes'][str(file.relative_to(ROOT))],file
for file in HERE.glob('*.lean'):
    assert not re.search(r'\b(?:sorry|axiom|native_decide)\b',file.read_text()),file
for file in [HERE/'README.md',HERE/'PROTOCOL.md',ROOT/'reports/real-closure-algebraic-experiment.md']:
    for link in re.findall(r'\]\(([^)]+)\)',file.read_text()):
        if '://' not in link:
            assert (file.parent/link.split('#')[0]).exists(),(file,link)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
print(json.dumps({'mathlib_free_noncore_imports':sorted(seen),
                  'timed_sources_match':True,'no_proof_holes':True,'relative_links_resolve':True},indent=2))
