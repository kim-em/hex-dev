from pathlib import Path
import gzip,hashlib,json,subprocess,sys
root=Path('/home/kim/.codex/tasks/hex-10358/boolean-worktree');task=root.parent
source=subprocess.check_output(['git','rev-parse',sys.argv[1]],cwd=root,text=True).strip()
out=root/'reports/data/hexrcf-cell-execution';out.mkdir(exist_ok=True,parents=True)
h=lambda b:hashlib.sha256(b).hexdigest()
paths=subprocess.check_output(['git','diff','--name-only','acbb63f376',source],cwd=root,text=True).splitlines()
owned=lambda p:p.startswith(('adapters/HexRCF/','conformance/HexRCF/','HexManual/Chapters/HexRCF/')) or p in {'adapters/HexRCF/RealCoefficients.lean','lakefile.lean','HexRCF/README.md','reports/hexrcf-adapter-evidence.md','reports/hexrcf-cell-execution.md','reports/hexrcf-cell-decision.md'}
sources={p:h(subprocess.check_output(['git','show',source+':'+p],cwd=root)) for p in paths if owned(p)}
def archive(name):
 data=(task/name).read_bytes();packet=gzip.compress(data,mtime=0);dest=out/(name+'.gz');dest.write_bytes(packet)
 return {'path':dest.name,'bytes':len(packet),'sha256':h(packet),'uncompressed_bytes':len(data),'uncompressed_sha256':h(data)}
checks=['operational-public-full-build-2.log','operational-manual-wrap-build-1.log','operational-public-manual-render-2.log','operational-public-manual-browser-2.log','operational-public-resource-limits.log','operational-final-links.log']+[f'operational-final-{n}.log' for n in ['dag','dag-tests','admissions','admission-tests','copyright','manual-split','literals','targets']]
for n in checks[:3]:assert b'Build completed successfully' in (task/n).read_bytes(),n
interim=['operational-public-build-1.log','operational-public-proof-2.log','operational-public-complete-3.log','operational-public-regressions-1.log','operational-public-kernel-1.log','operational-public-manual-1.log','operational-review-build-1.log','operational-review-proof-1.log','operational-review-trace-1.log','operational-review-sharing-1.log','operational-review-audits-1.log','operational-review-kernel-1.log','operational-review-final-1.log','operational-public-manual-render-1.log']
retained={'operational-public-manual-browser-1.log':'At source 8d5fdb0ebec9814a12bacd6c73655d99e675eb5a, the strengthened manual example overflowed by 84 pixels on a 390-pixel viewport. Retained captures and geometry accompany this failure; dc850edeb4 wraps the example without changing its proposition.', 'operational-public-full-build-1.log':'Interrupted at fa6d418190 to address substantive review findings about prepared-query reuse, exact producer traces and quotation-import evidence. Not a successful full build.','operational-public-proof-1.log':'Point variable shadowed the function name and cross-module build body was not exposed; corrected before successful proof validation.','operational-public-complete-1.log':'The returned-packet statement needed explicit canonical hashing instances.','operational-public-complete-2.log':'The rewrite needed to expose the actual build definition and match local context aliases before applying the producer equation.'}
artifacts=[]
for label in ['desktop','narrow']:
 for kind in ['source','binding','scope']:
  name=f'cell-execution-{label}-{kind}.png';data=(task/'boolean-render'/name).read_bytes();(out/name).write_bytes(data)
  artifacts.append({'path':name,'bytes':len(data),'sha256':h(data)})
for name in ['cell-execution-inspection.json','cell-execution-browser.mjs']:
 data=(task/'boolean-render'/name).read_bytes();(out/name).write_bytes(data);artifacts.append({'path':name,'bytes':len(data),'sha256':h(data)})
for entry in sorted((task/'boolean-render'/'cell-execution-overflow-attempt').iterdir()):
 data=entry.read_bytes();name='attempt-1-'+entry.name;(out/name).write_bytes(data);artifacts.append({'path':name,'bytes':len(data),'sha256':h(data),'source_commit':'8d5fdb0ebec9814a12bacd6c73655d99e675eb5a','scope':'Retained failed narrow-screen inspection before wrapping.'})
collector=Path(__file__).read_bytes();(out/'collect.py').write_bytes(collector)
artifacts.append({'path':'collect.py','bytes':len(collector),'sha256':h(collector)})
context={'schema':1,'source_commit':source,'selected_source_hashes':sources,'full_build_commit':'8d5fdb0ebec9814a12bacd6c73655d99e675eb5a','successful_checks':[dict(archive(n),source_commit=source if n in {'operational-manual-wrap-build-1.log','operational-public-manual-render-2.log','operational-public-manual-browser-2.log'} else '8d5fdb0ebec9814a12bacd6c73655d99e675eb5a') for n in checks],'interim_scope':'These checks belong to earlier implementation/review stages and do not attest the final source. The initial public proof/build checks precede the 4c996cd370 fixes; operational-review-kernel-1 predates the 108e35ede2 cleanup; operational-review-final-1 checks 108e35ede2 before the subsequent main merge. The first manual render passed at 8d5fdb0ebec9814a12bacd6c73655d99e675eb5a before the retained narrow-screen failure; the final render checks the wrapped example.','interim_checks':[archive(n) for n in interim],'retained_attempts':[dict(archive(n),reason=r) for n,r in retained.items()],'visual_artifacts':artifacts,'limits':{'aggregate_memory_bytes':34359738368,'swap_bytes':0,'lean_threads':2,'concurrent_own_builds':1},'scope':'Actual native ordinary-model construction, exact candidate-vector and typed-producer equations, frozen equality and both original shared-sentence verdicts. Not general literal-reader, frozen-history, strict missing-record, named-model or frontend acceptance.'}
(out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print('Bound',len(sources),'implementation files,',len(checks),'final checks,',len(interim),'interim checks,',len(retained),'retained attempts and',len(artifacts),'visual artifacts to',source)
