from pathlib import Path
import gzip, hashlib, json, re, shutil, subprocess

repo = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10358')
task = Path('/home/kim/.codex/tasks/hex-10358')
render = task / 'scalar-review-render'
out = repo / 'reports/data/hexrcf-source-selection'
out.mkdir(parents=True, exist_ok=True)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=repo, text=True).strip()

integration = (task/'source-selection-integration-8.log').read_text()
assert 'Build completed successfully' in integration
assert 'status=0/SUCCESS' in integration
rendered = (task/'source-selection-render-7.log').read_text()
assert 'Build completed successfully' in rendered
assert 'status=0/SUCCESS' in rendered
browser = (task/'source-selection-browser-5.log').read_text()
assert 'Saved source-selection desktop/narrow screenshots' in browser
assert 'status=0/SUCCESS' in browser
audit = re.search(r'source-selection inspection: (\d+) theorem bodies/(\d+) definitions; (\d+) nonempty traces', integration)
assert audit
generic = re.search(r'source selection: (\d+) exported theorem bodies checked in a fresh module', integration)
assert generic
cap = (task/'source-selection-cap-final.txt').read_text()
assert 'ActiveState=active' in cap
assert 'MemoryMax=34359738368' in cap and 'MemorySwapMax=0' in cap

artifacts = []
def save(path, data, raw=None):
    target = out/path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    item = {'path': path, 'bytes': len(data), 'sha256': sha(data)}
    if raw is not None:
        item['uncompressed_sha256'] = sha(raw)
    artifacts.append(item)

for log in sorted(task.glob('source-selection-*.log')):
    raw = log.read_bytes()
    save('logs/'+log.name+'.gz', gzip.compress(raw, mtime=0), raw)
for log in sorted(task.glob('source-selection-*.json')):
    if 'captures-opened-2' in log.name:
        continue
    save('records/'+log.name, log.read_bytes())
for name in ['source-selection-cap-final.txt', 'source-selection-browser.mjs']:
    save('scripts/'+name, (task/name).read_bytes())
save('scripts/run-bounded.sh', (task/'bin/run-bounded').read_bytes())
save('scripts/ScalarReviewRender.lean.txt', (render/'ScalarReviewRender.lean').read_bytes())
save('scripts/lakefile.lean.txt', (render/'lakefile.lean').read_bytes())
save('scripts/SourceSelectionEmitter.lean.txt', (render/'SourceSelectionEmitter.lean').read_bytes())
save('scripts/SourceSelectionProbe.lean.txt', (render/'SourceSelectionProbe.lean').read_bytes())
save('scripts/collect-source-selection.py', Path(__file__).read_bytes())
for directory, label in [(render/'archive-source-selection-1','initial-b22'), (render/'archive-source-selection-2','failed-f6d780'), (render/'archive-source-selection-3','prior-33ab'), (render/'archive-source-selection-4','prior-af95'), (render,'final')]:
    for path in sorted(directory.glob('source-selection-*')):
        if path.is_file() and path.suffix in ('.json','.png'):
            save('manual/'+label+'/'+path.name, path.read_bytes())

receipt = json.loads((task/'source-selection-captures-opened-2.json').read_text())
assert len(receipt['images']) == 8
for entry in receipt['images']:
    image = render/entry['name']
    assert entry['sha256'] == sha(image.read_bytes())
save('records/source-selection-captures-opened-2.json',
     (task/'source-selection-captures-opened-2.json').read_bytes())

changed = git('diff','--name-only','origin/main...HEAD').splitlines()
extras = ['HexRCF.lean','lean-toolchain',
    'conformance/HexRCF/NativeSelectionLiterals.lean',
    'conformance/HexRCF/NativeSamplesConformance.lean',
    'conformance/HexRCF/SelectedRoot/KernelCheck.lean']
sources = {name: sha((repo/name).read_bytes()) for name in sorted(set(changed+extras))
    if not name.startswith('reports/')}
record = {
    'rendered_html_sha256': sha((render/'scalar-review-html/html-single/index.html').read_bytes()),
    'source_commit': git('rev-parse','HEAD'),
    'source_tree': git('rev-parse','HEAD^{tree}'),
    'sources': sources,
    'validation': {
        'quotation_nodes': {label: int(re.search(re.escape(label) + r' proofNodes=(\d+)', integration).group(1)) for label in ['source-selection root quotation', 'source-header binding', 'negative-source root quotation', 'negative-source header binding']},
        'integration': 'logs/source-selection-integration-8.log.gz',
        'fresh_audit': 'logs/source-selection-audit-review-2.log.gz',
        'audit': dict(zip(['theorem_bodies','definitions','nonempty_traces'],map(int,audit.groups()))),
        'generic_bodies': int(generic.group(1)),
        'render': 'logs/source-selection-render-7.log.gz',
        'browser': 'logs/source-selection-browser-5.log.gz',
        'live_cap': 'scripts/source-selection-cap-final.txt',
    },
    'render_cancelled': {
        'log': 'logs/source-selection-render-2.log.gz',
        'classification': 'cancelled, signal15/TERM; no completed Lake build despite systemd stop reporting outer success',
        'reason': 'substantive review findings required further source and manual changes',
    },
    'failed_browser': {'log': 'logs/source-selection-browser-2.log.gz', 'source_commit': 'f6d780d440', 'overflow_pixels': 5, 'artifacts': 'manual/failed-f6d780', 'resolution': 'wrap the Lean declaration; retain the same >1px failure threshold'},
    'body_scope': re.findall(r'`([A-Za-z0-9_.]+)', re.search(
        r'unless #\[(.*?)\]\.contains modules\[index\]!',
        (repo/'conformance/HexRCF/SourceSelectionKernel.lean').read_text(), re.S).group(1)),
    'legacy_scope': 'native fixture construction excluded from body diagnostics, included in complete axiom closure',
    'observations': 'Reused-dependency build validation only; no complexity, speedup or physical-sharing claim',
    'artifacts': sorted(artifacts,key=lambda x:x['path']),
}
(out/'context.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'source_commit':record['source_commit'],'artifacts':len(artifacts),'audit':record['validation']['audit']}))
