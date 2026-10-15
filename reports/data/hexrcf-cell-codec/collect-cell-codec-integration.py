from pathlib import Path
import gzip,hashlib,json,subprocess,shutil
root=Path.cwd();scratch=Path('/home/kim/.codex/tasks/hex-10358');out=root/'reports/data/hexrcf-cell-codec';commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();h=lambda b:hashlib.sha256(b).hexdigest()
changed=subprocess.check_output(['git','diff','--name-only','origin/main...HEAD'],text=True).splitlines();sources=[p for p in changed if p.endswith('.lean') or p=='HexRCF/README.md']
for log,needle in [('cell-codec-review-integrated-build-1.log',b'Build completed successfully (11769 jobs)'),('complete-packet-manual-render-3.log',b'Build completed successfully (14294 jobs)'),('complete-packet-manual-browser-3.log',b'Saved complete-packet desktop/narrow screenshots')]:
 raw=(scratch/log).read_bytes();assert needle in raw and b'status=0/SUCCESS' in raw,log
logs={}
for pattern in ['cell-codec-review-*.log','complete-packet-manual-*.log','number-field-complete-*.log']:
 for p in sorted(scratch.glob(pattern)):
  raw=p.read_bytes();dest=out/(p.name+'.gz');dest.write_bytes(gzip.compress(raw,mtime=0));logs[dest.relative_to(root).as_posix()]={'sha256':h(dest.read_bytes()),'uncompressed_sha256':h(raw)}
artifacts={}
def copy(src,dest):
 dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dest);artifacts[dest.relative_to(root).as_posix()]=h(dest.read_bytes())
for attempt in [1,2]:
 for p in sorted((scratch/f'complete-packet-layout-attempt-{attempt}').iterdir()):copy(p,out/f'layout-attempt-{attempt}'/p.name)
render=scratch/'boolean-render'
for p in sorted(render.glob('complete-packet-*.png')):copy(p,out/p.name)
copy(render/'complete-packet-inspection.json',out/'complete-packet-inspection.json')
copy(scratch/'complete-packet-browser.mjs',out/'complete-packet-browser.mjs')
# Bind the literal HTML viewed without adding its large generated page to source.
html=render/'full-html/html-single/index.html'
inspection=json.loads((render/'complete-packet-inspection.json').read_text());assert len(inspection)==8
assert all(x['targetScrollWidth']<=x['targetWidth']+1 and x['descendantOverflow']<=1 for x in inspection)
d={'source_commit':commit,'emitted_packet_source_commit':'66e99e4cf1','sources_sha256':{p:h(subprocess.check_output(['git','show',commit+':'+p])) for p in sources},'logs':logs,'artifacts_sha256':artifacts,'rendered_html_sha256':h(html.read_bytes()),'validation':{'serialization_actual_bodies':21,'execution_actual_bodies':13,'typed_decision_bodies':28,'discovery_bodies':9,'selected_field_bodies':5,'new_original_source_bodies':2,'separate_domain_body':1,'final_selected_build_jobs':11769,'manual_render_jobs':14294,'final_captures':8,'scan_cones':641,'scan_modules':1541,'memory_bytes':34359738368,'swap_bytes':0,'lean_threads':2,'own_build_concurrency':1},'limits':['Complete-packet acceptance uses the actual emitted rootGraph and cells and native context codec law; frozen predecessor/provider histories are not reconstructed.','Re-encoded fixture bytes match the frozen artifact in a compiled control; kernel source proofs still use checked typed data and finite codec laws, not a new literal-reader reduction.','Partial restricted-reader inventories are tested in compiled regressions; there is no new genuinely partial reader kernel fixture.','The final integrated build reuses typed/Boolean source quotations rebuilt by the retained preceding11768-job build.','The initial import-removal, dsimp and zero-preflight test failures and both overflowing layout attempts are retained.','Operational build/render observations are not a performance comparison or frontend completeness evidence.']}
(out/'integration-context.json').write_text(json.dumps(d,indent=2)+'\n');print(commit,len(sources),'sources',len(logs),'logs',len(artifacts),'artifacts')
