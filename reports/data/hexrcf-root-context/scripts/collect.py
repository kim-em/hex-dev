"""Retain completed native context validation and bind it to committed sources."""
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

validation = {'integration': 'root-context-final-integration-4.log',
              'manual': 'root-context-final-integration-4.log',
              'controls': 'root-context-final-integration-4.log',
              'render': 'root-context-render-3.log', 'browser': 'root-context-browser-8.log'}
for key, name in validation.items():
    text = (args.task_root / name).read_text()
    assert 'status=0/SUCCESS' in text, name
    assert ('Saved root-context desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, name
    keep(args.task_root / name, 'validation/' + name + '.gz')
metadata_path = args.task_root / 'root-context-final-metadata-results-3.json'
metadata = json.loads(metadata_path.read_text())
assert all(item['exit_code'] == 0 for item in metadata)
keep(metadata_path, 'validation/metadata.json')
for item in metadata:
    keep(args.task_root / item['log'], 'validation/' + item['log'] + '.gz')
keep(args.task_root / 'root-context-memory-policy.txt', 'validation/memory-policy.txt.gz')
keep(args.task_root / 'bin' / 'run-bounded', 'scripts/run-bounded')
for pattern in ['root-context-production-*.log', 'root-context-integration-1.log',
                'root-context-browser-[1-7].log', 'root-context-render-[12].log',
                'root-context-final-integration-[1-3].log', 'root-context-manual-width-1.log',
                'frozen-signature-*.log']:
    for source in sorted(args.task_root.glob(pattern)):
        keep(source, 'diagnostics/' + source.name + '.gz')
keep(args.render_root / 'ScalarReviewRender.lean', 'scripts/render-main.lean.txt')
for source in sorted(args.render_root.glob('root-context-*.png')):
    keep(source, 'captures/' + source.name)
for source in sorted(args.render_root.glob('root-context-*.json')):
    keep(source, 'captures/' + source.name)
prior = json.loads((root.parent / 'hexrcf-root-header' / 'context.json').read_text())
baseline = 'e92beebc18c626ad94d0e64791b23239cdfdb9bb'
changed = git('diff', '--name-only', baseline, args.source).decode().splitlines()
paths = set(prior['sources']) | {p for p in changed if not p.startswith('reports/')} | {
    'HexRCF/SPEC/hex-rcf.md', 'SPEC/real-closure-execution.md', 'libraries.yml',
    'adapters/HexRCF/RealCoefficients/RealModel.lean',
    'adapters/HexRealClosureTheory/TowerModel.lean', 'HexRealClosure/ContextData.lean'}
source = git('show', args.source + ':conformance/HexRCF/RootContextProofs.lean').decode()
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
    'audit_counts': [682, 68, 735],
    'header_counts': [674, 66, 725],
    'signature_counts': [23, 7, 16],
    'report_sha256': sha((repo / 'reports/hexrcf-root-context.md').read_bytes()),
    'reports': {name: sha((repo / name).read_bytes()) for name in [
        'reports/hexrcf-root-context.md', 'reports/hexrcf-root-header-quotation.md']},
    'diagnostics': {
        'root-context-final-integration-1.log': 'passed earlier context integration before full literal codec adoption',
        'root-context-final-integration-3.log': 'passed functional full build at8092a1eec0 before module docstrings and narrow example wrapping',
        'root-context-final-integration-2.log': 'operator-stopped superseded manual pass; completed conformance/audits retained; signal15/TERM and no completed full build, not a passing sample',
        'frozen-signature-packet-1.log': 'failed direct rational signature literal rfl; public signature/keys laws required',
        'frozen-signature-packet-2.log': 'failed rewrite through rational context alias; fixed by explicit public definition unfolding',
        'frozen-signature-packet-3.log': 'failed isolated fixture meta-only import and Option.none pattern; full packet projection still unrecognized',
        'frozen-signature-packet-4.log': 'isolated signatures passed; full packet projection unrecognized; diagnostic messages restored by transaction',
        'frozen-signature-packet-5.log': 'full packet projection unrecognized; diagnostic messages restored by transaction',
        'frozen-signature-packet-6.log': 'retained IO diagnostic identified Vector-index payload; failed exact payload match before projection reduction',
        'frozen-signature-packet-7.log': 'passed full frozen packet before constructor-only source assertion',
        'frozen-signature-audit-1.log': 'isolated audit passed; literal syntax guard rejected numeral wrappers',
        'frozen-signature-literal-constructors-1.log': 'isolated pinned audit passed; source guard identified OfNat/Neg wrappers',
        'frozen-signature-projected-1.log': 'projected integer-constructor comparison failed; source guard also found Nat numeral wrappers',
        'frozen-signature-projected-2.log': 'projected case passed with instance transparency; source guard found Nat numeral wrappers',
        'frozen-signature-audit-2.log': 'all producer guards and five packet controls passed; inventory pins required 23/7/16,674/66/725,682/68/735',
        'root-context-production-cases-1.log': 'failed: missing mkOfNat quotation API',
        'root-context-production-cases-2.log': 'failed: public export inferred private proof type in exporting scope',
        'root-context-production-cases-3.log': 'passed preliminary controls before unresolved-input regression',
        'root-context-production-audit-1.log': 'preliminary audit before exported public model',
        'root-context-browser-1.log': 'failed harness whitespace match',
        'root-context-browser-2.log': 'failed harness escaped whitespace match',
        'root-context-browser-3.log': 'failed harness escaped whitespace match; retained document diagnostics',
        'root-context-browser-4.log': 'failed harness escaped whitespace match; diagnostic snippet',
        'root-context-browser-5.log': 'failed harness escaped whitespace match; captured normalized body revealed literal-s substitution',
        'root-context-browser-6.log': 'failed: narrow code block overflow, fixed by local namespace opens'},
    'artifacts': []}
for path in sorted(root.rglob('*')):
    if not path.is_file() or path.name == 'context.json' or '__pycache__' in path.parts:
        continue
    raw = path.read_bytes()
    item = {'path': path.relative_to(root).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}
    if path.suffix == '.gz':
        item['uncompressed_sha256'] = sha(gzip.decompress(raw))
    record['artifacts'].append(item)
(root / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(f"Retained {len(record['artifacts'])} artifacts against {len(record['sources'])} sources")
