from pathlib import Path
import gzip, hashlib, json, subprocess
root=Path('/home/kim/.codex/tasks/hex-10358/boolean-worktree')
task=root.parent
out=root/'reports/data/hexrcf-field-cells';out.mkdir(parents=True,exist_ok=True)
revision=lambda x:subprocess.check_output(['git','rev-parse',x],cwd=root,text=True).strip()
implementation=revision('5b489eee3d');source=revision('abae613acf')
h=lambda b:hashlib.sha256(b).hexdigest()
paths=['adapters/HexRCF/RealCoefficients/NumberFieldCells.lean','conformance/HexRCF/NumberFieldCellsConformance.lean','adapters/HexRCF/RealCoefficients.lean','lakefile.lean','HexManual/Chapters/HexRCF/AlgebraicCells.lean','HexRCF/README.md','reports/hexrcf-cell-execution.md']
source_hashes={p:h(subprocess.check_output(['git','show',source+':'+p],cwd=root)) for p in paths}
def archive(name):
 raw=(task/name).read_bytes();data=gzip.compress(raw,mtime=0);dest=name+'.gz';(out/dest).write_bytes(data)
 return {'path':dest,'bytes':len(data),'sha256':h(data),'uncompressed_bytes':len(raw),'uncompressed_sha256':h(raw)}
checks=['number-field-cells-public-2.log','number-field-cells-manual-wrap-1.log','number-field-cells-manual-render-2.log','number-field-cells-manual-browser-2.log']+[f'number-field-cells-{n}.log' for n in ['dag-1','admissions-1','copyright-3','dag-tests-2','admission-tests-2','manual-split-2','literals-1','targets-1']]
for name in checks[:3]:assert b'Build completed successfully' in (task/name).read_bytes(),name
assert b'Saved number-field-cells desktop/narrow screenshots' in (task/checks[3]).read_bytes()
successful=[dict(archive(n),source_commit=source if n in checks[1:4] else implementation) for n in checks]
interim=['field-cells-prototype-1.log','field-cells-prototype-2.log','field-cells-prototype-5.log','field-cells-native-2.log','number-field-cells-public-1.log','number-field-cells-manual-render-1.log']
retained={
 'field-cells-prototype-3.log':'Scratch attempt used unqualified decide in the RCF namespace; it resolved to the sentence decision function. No failed declaration entered the public module.',
 'field-cells-prototype-4.log':'Scratch zero-preflight proof simplified the all predicate before applying its false equation. Fixed by rewriting before reduction.',
 'field-cells-native-1.log':'Both native cases ran, but the module failed on an unqualified logInfo in its audit block. The corrected native-2 run includes the actual completed audit.',
 'number-field-cells-manual-browser-1.log':'At the implementation commit, the new 390-pixel code target overflowed by15 pixels. Geometry and four captures are retained; the final source wraps this line.',
 'number-field-cells-admission-tests-1.log':'Incorrect unittest import path in ROOT, not the source worktree; the later discover invocation in the correct worktree passes.',
 'number-field-cells-dag-tests-1.log':'Passed in ROOT rather than the source worktree; retained but not evidence for the final source. The correctly scoped -2 run is final.',
 'number-field-cells-copyright-2.log':'Passed in ROOT rather than the source worktree; retained but not evidence for the new files. The correctly scoped -3 run is final.',
 'number-field-cells-manual-split-1.log':'Passed in ROOT rather than the source worktree; retained but not evidence for the final source. The correctly scoped -2 run is final.'}
artifacts=[]
def copy(path,name,**extra):
 data=path.read_bytes();(out/name).write_bytes(data);artifacts.append({'path':name,'bytes':len(data),'sha256':h(data),**extra})
for label in ['desktop','narrow']:
 for kind in ['source','binding','scope']:
  name=f'number-field-cells-{label}-{kind}.png';copy(task/'boolean-render'/name,name,source_commit=source)
for name in ['number-field-cells-inspection.json','number-field-cells-browser.mjs']:
 copy(task/'boolean-render'/name,name,source_commit=source)
inspection=json.loads((out/'number-field-cells-inspection.json').read_text());assert len(inspection)==6
assert all(e['descendantOverflow']==0 and e['targetScrollWidth']<=e['targetWidth']+1 for e in inspection)
for path in sorted((task/'boolean-render/number-field-cells-overflow-attempt').iterdir()):
 copy(path,'attempt-1-'+path.name,source_commit=implementation,scope='Retained failed narrow-screen pass.')
for name in ['lake-bounded','run-bounded']:copy(task/'bin'/name,name+'.sh')
copy(Path(__file__),'collect.py')
context={'schema':1,'source_commit':source,'implementation_commit':implementation,'baseline_context':'../hexrcf-cell-execution/context.json','selected_source_hashes':source_hashes,'successful_checks':successful,'interim_scope':'Earlier scratch and public checks have their own narrower scope and do not attest the final manual. The public-1 implementation and conformance match the implementation commit. The first render passed at that commit before the retained visual failure.','interim_checks':[archive(n) for n in interim],'retained_attempts':[dict(archive(n),reason=reason) for n,reason in retained.items()],'artifacts':artifacts,'limits':{'aggregate_memory_bytes':34359738368,'swap_bytes':0,'lean_threads':2,'concurrent_own_builds':1},'scope':'Actual selected-number-field factory and complete-cell production, exact original Coefficients.ofField semantics, original guard preflight and three generic ordinary-kernel proof audits. Concrete positive/negative quadratic and computed cubic native round trips are regressions, not arbitrary finite-codec kernel acceptance, source reification or frontend completeness.'}
(out/'context.json').write_text(json.dumps(context,indent=2)+'\n')
print(len(source_hashes),'source hashes;',len(successful),'final checks;',len(interim),'interim checks;',len(retained),'retained attempts;',len(artifacts),'artifacts; source',source)
