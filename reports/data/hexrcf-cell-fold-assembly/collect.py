from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path.cwd();scratch=Path('/home/kim/.codex/tasks/hex-10358');out=root/'reports/data/hexrcf-cell-fold-assembly';out.mkdir(parents=True,exist_ok=True)
hashbytes=lambda x:hashlib.sha256(x).hexdigest()
source_commit='eec8df2e18233a37fccb323c9799cf954e99b265'
imports=json.loads((scratch/'cell-fold-imports.json').read_text())
sources={v['path']:v['sha256'] for v in imports['local_sources'].values()}
for name in ['conformance/HexRCF/CellReplay/Algebraic/Boolean.lean','HexManual/Chapters/HexRCF/AlgebraicCells.lean','lean-toolchain','lake-manifest.json','lakefile.lean']:
 sources[name]=hashbytes(subprocess.check_output(['git','show',source_commit+':'+name]))
for name,digest in sources.items():assert hashbytes(subprocess.check_output(['git','show',source_commit+':'+name]))==digest,name
files=['cell-check-diagnostic.py','cell-check-diagnostic-1.json','cell-check-diagnostic-1.original.json','cell-fold-pair.py','cell-fold-pair.json','cell-fold-pair-A.lean.txt','cell-fold-pair-B.lean.txt','cell-fold-imports.py','cell-fold-imports.json','ci-38721246777-final-jobs.json']
logs=['cell-check-diagnostic-1.log','cell-fold-kernel-only-smoke-1.log','cell-fold-boolean-kernel-only-smoke-1.log','cell-fold-current-manual-1.log','ci-38721246777-failed.log']+[f'cell-fold-pair-{trial}-{arm}.log' for trial in [0,1] for arm in ['A','B']]
artifacts={};compressed={}
for name in files:
 data=(scratch/name).read_bytes();p=out/name;p.write_bytes(data);artifacts[p.relative_to(root).as_posix()]=hashbytes(data)
for name in logs:
 data=(scratch/name).read_bytes();p=out/(name+'.gz');p.write_bytes(gzip.compress(data,mtime=0));compressed[p.relative_to(root).as_posix()]={'sha256':hashbytes(p.read_bytes()),'uncompressed_sha256':hashbytes(data)}
record={'source_commit':source_commit,'baseline_commit':'a66196ce7a39d21a107a2baad32d158fb3245d51','measurement_context_commit':'5da4aa647ee82620cf23a296f1a0d089bc063eed','sources_sha256':sources,'artifacts_sha256':artifacts,'compressed_logs':compressed,'validation':{'manual_target':'HexManual.Chapters.HexRCF.AlgebraicCells','manual_log':'cell-fold-current-manual-1.log','quoted_target':'HexRCF.CellReplay.Algebraic.BooleanQuoted','quoted_log':'cell-fold-boolean-kernel-only-smoke-1.log','local_imports_matched':918,'samples':4,'schedule':'AB/BA','cpu':23,'memory_limit_bytes':34359738368,'swap_limit_bytes':0,'lean_threads':2,'own_build_concurrency':1},'limits':['Two paired trials are inconclusive about repeatable speedup or general memory improvement.','Unmatched standalone peaks do not establish halved memory use.','Both variants perform the same decisive guarded kernel reduction.','The CI SIGTERM cause is unproven.','Sampled cgroup peak and whole-module bytes have their stated scope.','The displayed manual text/styles are unchanged; no new rendering claim.']}
(out/'context.json').write_text(json.dumps(record,indent=2)+'\n')
print(len(sources),'versioned source bindings',len(artifacts),'copied artifacts',len(compressed),'gzip logs')
