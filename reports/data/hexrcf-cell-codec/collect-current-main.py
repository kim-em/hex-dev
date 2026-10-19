from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path.cwd();scratch=Path('/home/kim/.codex/tasks/hex-10358');out=root/'reports/data/hexrcf-cell-codec';out.mkdir(parents=True,exist_ok=True)
commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
prior=json.loads((out/'context.json').read_text());paths=list(prior['sources_sha256'])
paths+=['HexSignDet/Codec/Coefficients.lean','HexSignDet/Codec/GraphLaws.lean','HexSignDet/Codec/Laws.lean','HexSignDet/Matrix.lean','conformance/HexRCF/CellReplay/Algebraic/Check.lean','conformance/HexRCF/CellReplay/Algebraic/Boolean.lean','conformance/HexRCF/SelectedRoot/KernelCheck.lean']
h=lambda b:hashlib.sha256(b).hexdigest();sources={name:h(subprocess.check_output(['git','show',commit+':'+name])) for name in dict.fromkeys(paths)}
logs={}
for name in ['cell-codec-current-main-integration-1.log','cell-codec-current-main-dag-1.log','cell-codec-current-main-admissions-1.log','cell-codec-current-main-copyright-1.log','cell-codec-current-main-literals-1.log','cell-codec-current-main-dag-tests-1.log','cell-codec-current-main-admission-tests-1.log']:
 raw=(scratch/name).read_bytes()
 if name=='cell-codec-current-main-integration-1.log':assert b'Build completed successfully' in raw and b'Main processes terminated with: code=exited, status=0/SUCCESS' in raw
 dest=out/(name+'.gz');dest.write_bytes(gzip.compress(raw,mtime=0));logs[dest.relative_to(root).as_posix()]={'sha256':h(dest.read_bytes()),'uncompressed_sha256':h(raw)}
record={'source_commit':commit,'integrated_main':'c7bd7e9047','integrated_issue_branch':'b1dc2e1d8ccc3a55322bcf05a28868e0e6b2090e','sources_sha256':sources,'logs':logs,'scope':'Optional adapter, six new actual serialization proof bodies, fifty retained audit entries, exact frozen fixture, selected-field source tests, fresh quotation modules, discovery/requested-cell regressions and importing manual chapter. Owner imports rebuilt after latest-main codec changes. Original partial-codec descriptor restoration remains a premise; no general acceptance or frontend completeness claim.','resource_limits':{'memory_bytes':34359738368,'swap_bytes':0,'lean_threads':2,'own_build_concurrency':1}}
(out/'current-main-context.json').write_text(json.dumps(record,indent=2)+'\n');print(commit,len(sources),'source bindings',len(logs),'successful logs')
