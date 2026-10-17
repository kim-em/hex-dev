"""Collect completed validation logs and bind them to a committed source tree."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
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


def sha(data):
    return hashlib.sha256(data).hexdigest()


def keep(source, target, compress=False):
    raw = source.read_bytes()
    path = root / target
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(gzip.compress(raw, mtime=0) if compress else raw)


validation = {
    'integration': 'public-packet-integration-2.log',
    'render': 'public-packet-render-1.log',
    'browser': 'public-packet-browser-2.log'}
for key, name in validation.items():
    text = (args.task_root / name).read_text()
    assert 'status=0/SUCCESS' in text, name
    assert ('Saved public-packet desktop/narrow screenshots' if key == 'browser'
            else 'Build completed successfully') in text, name
    keep(args.task_root / name, 'validation/' + name + '.gz', True)

# This target passed, although other targets made its enclosing build fail.
# Preserve that distinction rather than classifying the whole build as green.
fresh = args.task_root / 'public-packet-integration-1.log'
assert 'Built HexRCF.PublicSignPacketProofs' in fresh.read_text()
keep(fresh, 'validation/public-packet-integration-1.log.gz', True)
for pattern in ['production-rootquote-*.log', 'production-dependent-*.log',
                'production-public-*.log', 'production-legacy-packet-*.log',
                'public-packet-browser-*.log', 'public-packet-metadata-*.log']:
    for source in sorted(args.task_root.glob(pattern)):
        keep(source, 'diagnostics/' + source.name + '.gz', True)
keep(args.task_root / 'public-packet-memory-policy.txt',
     'validation/public-packet-memory-policy.txt.gz', True)
metadata = args.task_root / 'public-packet-metadata-results-3.json'
assert all(item['exit_code'] == 0 for item in json.loads(metadata.read_text()))
keep(metadata, 'validation/metadata-results-3.json')
for source in sorted(args.render_root.glob('public-packet-*.png')):
    keep(source, 'captures/' + source.name)
for source in sorted(args.render_root.glob('public-packet-*.json')):
    keep(source, 'captures/' + source.name)

baseline = 'e0faead2f34b3b4379dd1c0ca0cfa1f2b1a2a43f'
source = git('rev-parse', args.source).decode().strip()
changed = git('diff', '--name-only', baseline, source).decode().splitlines()
paths = [path for path in changed if not path.startswith('reports/')]
guards = ['conformance/HexRCF/SelectedRoot/KernelCheck.lean',
          'experiments/KernelReplay/AxiomClosure.lean', 'AGENTS.md', 'PLAN.md',
          '.github/workflows/ci.yml']
paths += guards + ['lean-toolchain', 'lake-manifest.json',
    'conformance/HexRCF/RootQuoteData.lean', 'conformance/HexRCF/RootQuoteCases.lean',
    'conformance/HexRCF/RootQuoteSource.lean',
    'adapters/HexRCF/RealCoefficients/ScalarPacket.lean',
    'adapters/HexRCF/RealCoefficients/ScalarQuote.lean',
    'adapters/HexRCF/RealCoefficients/RationalQuote.lean',
    'HexRealClosure/TowerContext.lean', 'HexRealClosure/Algebraic.lean',
    'HexRealClosure/SignFacts.lean', 'HexRealClosure/SignCodec.lean',
    'adapters/HexRealClosureTheory/SignFacts.lean',
    'adapters/HexRealClosureTheory/Algebraic.lean']
sources = {}
for path in sorted(set(paths)):
    raw = git('show', source + ':' + path)
    assert raw == (repo / path).read_bytes(), path
    sources[path] = sha(raw)
artifacts = []
for path in sorted(root.rglob('*')):
    if not path.is_file() or path.name == 'context.json':
        continue
    raw = path.read_bytes()
    item = {'path': str(path.relative_to(root)), 'bytes': len(raw), 'sha256': sha(raw)}
    if path.suffix == '.gz':
        item['uncompressed_sha256'] = sha(gzip.decompress(raw))
    artifacts.append(item)
record = {
    'source_commit': source,
    'source_tree': git('rev-parse', source + '^{tree}').decode().strip(),
    'baseline_commit': baseline, 'sources': sources, 'unchanged_guards': guards,
    'artifacts': artifacts, 'audit_counts': [646, 67, 703],
    'body_scope': ['HexRCF.PublicSignPacket', 'HexRCF.PublicSignPacketValues',
        'HexRCF.RealCoefficients.RootQuote', 'HexRCF.RootQuoteCases',
        'HexRCF.RootQuoteSource', 'HexRCF.RootQuoteData',
        'HexRCF.RealCoefficients.ScalarPacket'],
    'validation': {**{key: 'validation/' + value + '.gz' for key, value in validation.items()},
        'fresh_target_in_failed_build': 'validation/public-packet-integration-1.log.gz',
        'metadata': 'validation/metadata-results-3.json',
        'memory': 'validation/public-packet-memory-policy.txt.gz'},
    'limits': ['Reused-dependency build observations, not scaling or speedup evidence.',
        'Canonical encoded context expressions, not fully frozen numerical signatures.',
        'Full axiom closure; imported-body diagnostics restricted to the stated module scope.',
        'Cancelled diagnostics and partial-target successes are not successful full builds.']}
(root / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'Collected {len(artifacts)} artifacts from {len(sources)} committed sources at {source}.')
