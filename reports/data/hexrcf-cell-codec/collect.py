from pathlib import Path
import gzip,hashlib,json,subprocess
root=Path.cwd(); scratch=Path('/home/kim/.codex/tasks/hex-10358')
out=root/'reports/data/hexrcf-cell-codec';out.mkdir(parents=True,exist_ok=True)
commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
changed=subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',commit],text=True).splitlines()
extra=['conformance/HexRCF/CellBuildConformance.lean','conformance/HexRCF/CellDecisionProofs.lean','conformance/HexRCF/CellDiscoverProofs.lean','conformance/HexRCF/CellExecutionProofs.lean','conformance/HexRCF/NumberFieldCellsConformance.lean','conformance/HexRCF/CellReplay/Algebraic/Quoted.lean','conformance/HexRCF/CellReplay/Algebraic/BooleanQuoted.lean','conformance/HexRCF/CellDiscoverLinear.lean','conformance/HexRCF/CellDiscoverAlgebraic.lean','conformance/HexRCF/CellDiscoverCases.lean','conformance/HexRCF/CellRequestedConformance.lean','HexManual/Chapters/HexRCF/AlgebraicCells.lean']
sha=lambda x:hashlib.sha256(x).hexdigest()
sources={p:sha(subprocess.check_output(['git','show',commit+':'+p])) for p in dict.fromkeys(changed+extra)}
logs={}
for pattern in ('sector-codec-proof-*.log','cell-codec-proof-*.log','cell-codec-audits-regressions-*.log','cell-codec-library-quotes-*.log','cell-codec-dag-*.log','cell-codec-admissions-*.log','cell-codec-copyright-*.log','cell-codec-checker-tests-*.log','cell-codec-admission-tests-*.log','cell-codec-literals-*.log'):
 for p in sorted(scratch.glob(pattern)):
  raw=p.read_bytes(); target=out/(p.name+'.gz');target.write_bytes(gzip.compress(raw,mtime=0))
  logs[target.relative_to(root).as_posix()]={'sha256':sha(target.read_bytes()),'uncompressed_sha256':sha(raw)}
record={'implementation_commit':commit,'sources_sha256':sources,'logs':logs,'validation':{'audits_regressions':'cell-codec-audits-regressions-4.log','optional_library_fresh_quotes_regressions_manual':'cell-codec-library-quotes-1.log','audited_theorems':6,'retained_prior_audit_bodies':50,'scan_cones':635,'scan_local_modules':1535,'checker_tests':22,'memory_limit_bytes':34359738368,'swap_limit_bytes':0,'lean_threads':2,'own_build_concurrency':1},'limitations':['Descriptor restoration is an explicit remaining owner premise.','Finite coverage and identical encoding are required for partial readers.','No general predecessor inventory, strict compiled admission or frontend completeness is claimed.','Build times are incremental operational observations, not a performance comparison.','Manual text/styles are unchanged; no new rendering claim is made.','Earlier failed proof attempts and the incorrect combined unittest invocation are retained.']}
(out/'context.json').write_text(json.dumps(record,indent=2)+'\n')
print(commit,len(sources),'source bindings',len(logs),'retained logs')
