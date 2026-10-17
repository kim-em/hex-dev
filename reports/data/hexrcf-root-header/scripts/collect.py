"""Retain completed root/header validation and bind it to committed sources."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--task-root', type=Path, required=True)
parser.add_argument('--render-root', type=Path, required=True)
parser.add_argument('--source', required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
repo = root.parents[2]

def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=repo)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def keep(source, destination):
    raw = source.read_bytes()
    target = root / destination
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(gzip.compress(raw, mtime=0) if target.suffix == '.gz' else raw)

validation = {'integration': 'root-header-integration-3.log',
              'budget': 'root-header-budget-usage-1.log',
              'render': 'root-header-render-1.log', 'browser': 'root-header-browser-1.log'}
for key, name in validation.items():
    text = (args.task_root / name).read_text()
    assert 'status=0/SUCCESS' in text, name
    assert ('Saved root-header desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, name
    keep(args.task_root / name, 'validation/' + name + '.gz')
metadata_path = args.task_root / 'root-header-final-metadata-results-1.json'
metadata = json.loads(metadata_path.read_text())
assert all(item['exit_code'] == 0 for item in metadata)
keep(metadata_path, 'validation/metadata.json')
for item in metadata:
    keep(args.task_root / item['log'], 'validation/' + item['log'] + '.gz')
keep(args.task_root / 'root-header-memory-policy.txt', 'validation/memory-policy.txt.gz')
keep(args.task_root / 'bin' / 'run-bounded', 'scripts/run-bounded')
for pattern in ['root-header-production-*.log', 'root-header-integration-[12].log',
                'header-current-core-1.log', 'header-packet-assembly-*.log',
                'header-packet-values-1.log', 'header-packet-controls-1.log',
                'header-controls-helper-order-1.log']:
    for source in sorted(args.task_root.glob(pattern)):
        keep(source, 'diagnostics/' + source.name + '.gz')
for name in ['HeaderQuote.lean', 'HeaderPacket.lean', 'HeaderPacketValues.lean',
             'HeaderPacketAudit.lean', 'HeaderControls.lean', 'SignatureRoundtrip.lean']:
    keep(args.task_root / 'header-assembly-validated' / name, 'diagnostics/' + name + '.txt.gz')
for source in sorted(args.render_root.glob('root-header-*.png')):
    keep(source, 'captures/' + source.name)
for source in sorted(args.render_root.glob('root-header-*.json')):
    keep(source, 'captures/' + source.name)
prior = json.loads((root.parent / 'hexrcf-dependent-quotation' / 'context.json').read_text())
baseline = '3b65efefa81e76a9f14db586db244b1c42d66fec'
changed = git('diff', '--name-only', baseline, args.source).decode().splitlines()
paths = set(prior['sources']) | set(changed) | {
    'HexRCF/SPEC/hex-rcf.md', 'SPEC/real-closure-execution.md', 'libraries.yml'}
source = git('show', args.source + ':conformance/HexRCF/RootHeaderProofs.lean').decode()
scope = re.search(r'let allowed := #\[(.*?)\]', source, re.S)
assert scope
record = {
    'source_commit': args.source,
    'source_tree': git('rev-parse', args.source + '^{tree}').decode().strip(),
    'baseline_commit': baseline,
    'sources': {path: sha(git('show', args.source + ':' + path)) for path in sorted(paths)},
    'unchanged_guards': prior['unchanged_guards'],
    'validation': {key: 'validation/' + name + '.gz' for key, name in validation.items()},
    'body_scope': re.findall(r'`([A-Za-z0-9_.]+)', scope.group(1)),
    'audit_counts': [665, 65, 720],
    'report_sha256': sha((repo / 'reports/hexrcf-root-header-quotation.md').read_bytes()),
    'diagnostics': {
        'root-header-production-core-1.log': 'failed: targets not registered in Lake yet',
        'root-header-production-public-1.log': 'passed preliminary source before final inventory and budget assertions',
        'root-header-integration-1.log': 'passed preliminary compatibility before final budget result fix',
        'root-header-integration-2.log': 'passed with pinned inventory; superseded by full final validation',
        'header-packet-assembly-1.log': 'failed prototype: doc comment attached to run_meta',
        'header-packet-assembly-2.log': 'failed prototype: audit syntax error',
        'header-packet-controls-1.log': 'packet controls passed, but enclosing build failed header-control namespace lookup'},
    'artifacts': []}
for path in sorted(root.rglob('*')):
    if not path.is_file() or path.name == 'context.json':
        continue
    raw = path.read_bytes()
    item = {'path': path.relative_to(root).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}
    if path.suffix == '.gz':
        item['uncompressed_sha256'] = sha(gzip.decompress(raw))
    record['artifacts'].append(item)
(root / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(f"Retained {len(record['artifacts'])} artifacts against {len(record['sources'])} sources")
