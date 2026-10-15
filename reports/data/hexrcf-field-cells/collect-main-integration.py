from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358');task=Path('/home/kim/.codex/tasks/hex-10358');out=root/'reports/data/hexrcf-field-cells'
source=subprocess.check_output(['git','rev-parse','6910dfddc5'],cwd=root,text=True).strip()
h=lambda b:hashlib.sha256(b).hexdigest()
changed=subprocess.check_output(['git','diff','--name-only','origin/main...'+source],cwd=root,text=True).splitlines()
paths=[p for p in changed if p.endswith('.lean') and (p.startswith(('adapters/HexRCF/','conformance/HexRCF/','HexManual/Chapters/HexRCF/')) or p=='lakefile.lean')]
sources={p:h(subprocess.check_output(['git','show',source+':'+p],cwd=root)) for p in paths}
names=['combined-cell-main-integration-build-1.log']+[f'combined-cell-main-{n}-1.log' for n in ['dag','admissions','dag-tests','admission-tests','copyright','manual-split','literals','targets']]
assert b'Build completed successfully' in (task/names[0]).read_bytes()
checks=[]
for n in names:
 raw=(task/n).read_bytes();data=gzip.compress(raw,mtime=0);p=n+'.gz';(out/p).write_bytes(data);checks.append({'path':p,'bytes':len(data),'sha256':h(data),'uncompressed_bytes':len(raw),'uncompressed_sha256':h(raw),'source_commit':source})
raw=Path(__file__).read_bytes();(out/'collect-main-integration.py').write_bytes(raw)
context={'schema':1,'source_commit':source,'main_parent':'1d19facf30','source_hashes':sources,'successful_checks':checks,'collector':{'path':'collect-main-integration.py','bytes':len(raw),'sha256':h(raw)},'core_context':'../hexrcf-cell-execution/context.json','selected_field_context':'context.json','scope':'Affected optional library,13 actual execution/source body audits, fresh algebraic/Boolean source quotations and affected manual built against actual merged main. This is separate from the earlier14,693-job full-target source. Target-list resolution preserves all344 entries. Earlier native/visual evidence retains its own source versions; no general finite-codec/frontend completeness or speedup claim.'}
(out/'main-integration-context.json').write_text(json.dumps(context,indent=2)+'\n')
print(len(sources),'current-main Lean source hashes;',len(checks),'successful integration logs; exact source',source)
