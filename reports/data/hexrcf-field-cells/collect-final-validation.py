from pathlib import Path
import subprocess,json,hashlib,gzip
root=Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358');task=Path('/home/kim/.codex/tasks/hex-10358');out=root/'reports/data/hexrcf-field-cells';source=subprocess.check_output(['git','rev-parse','9ca6964dd5'],cwd=root,text=True).strip();h=lambda b:hashlib.sha256(b).hexdigest()
changed=subprocess.check_output(['git','diff','--name-only','89ea00f7c5',source],cwd=root,text=True).splitlines();sources={p:h(subprocess.check_output(['git','show',source+':'+p],cwd=root)) for p in changed}
checks=['combined-review-api-audits-1.log','combined-review-affected-build-1.log','combined-review-manual-render-1.log','combined-review-core-browser-1.log','combined-review-field-browser-1.log']+[f'combined-review-{n}-1.log' for n in ['dag','admissions','dag-tests','admission-tests','copyright','manual-split','literals']]
for name in checks[:3]:assert b'Build completed successfully' in (task/name).read_bytes(),name
for name in checks[3:5]:assert b'Saved ' in (task/name).read_bytes(),name
def archive(name):
 raw=(task/name).read_bytes();b=gzip.compress(raw,mtime=0);dest=name+'.gz';(out/dest).write_bytes(b);return {'path':dest,'bytes':len(b),'sha256':h(b),'uncompressed_bytes':len(raw),'uncompressed_sha256':h(raw)}
artifacts=[]
for prefix in ['cell-execution','number-field-cells']:
 for label in ['desktop','narrow']:
  for kind in ['source','binding','scope']:
   name=f'{prefix}-{label}-{kind}.png';b=(task/'manual-render'/name).read_bytes();dest='final-'+name;(out/dest).write_bytes(b);artifacts.append({'path':dest,'bytes':len(b),'sha256':h(b)})
 name=prefix+'-inspection.json';b=(task/'manual-render'/name).read_bytes();data=json.loads(b);assert len(data)==6;assert all(e['descendantOverflow']==0 and e['targetScrollWidth']<=e['targetWidth']+1 for e in data);dest='final-'+name;(out/dest).write_bytes(b);artifacts.append({'path':dest,'bytes':len(b),'sha256':h(b)})
 name=prefix+'-browser.mjs';b=(task/'manual-render'/name).read_bytes();dest='final-'+name;(out/dest).write_bytes(b);artifacts.append({'path':dest,'bytes':len(b),'sha256':h(b)})
b=Path(__file__).read_bytes();(out/'collect-final-validation.py').write_bytes(b);artifacts.append({'path':'collect-final-validation.py','bytes':len(b),'sha256':h(b)})
context={'schema':1,'source_commit':source,'selected_source_hashes':sources,'successful_checks':[archive(n) for n in checks],'artifacts':artifacts,'scope':'Expanded incremental validation after removing unused hashing parameters, excluding RootBuild from both quotation import closures, pinning its declaration ownership and clarifying documentation. The13 selected build targets include all four audit groups(28+9+10+3 actual bodies), fixture byte equality, linear/algebraic/discovery/requested regressions, fresh original-source quotations and the affected manual. Earlier scoped artifacts and observations remain unchanged. This does not prove general finite-codec or frontend completeness.','limits':{'memory_bytes':34359738368,'swap_bytes':0,'lean_threads':2,'concurrent_own_builds':1}}
(out/'final-validation-context.json').write_text(json.dumps(context,indent=2)+'\n');print(len(sources),'source hashes;',len(checks),'final logs;',len(artifacts),'visual/support artifacts')
