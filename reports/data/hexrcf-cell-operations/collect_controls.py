#!/usr/bin/env python3
"""Bind expanded replay controls without changing the retained baseline."""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('source')
parser.add_argument('--task-dir', type=Path, default=Path('/home/kim/.codex/tasks/hex-10358'))
parser.add_argument('--record', default='controls-context.json')
parser.add_argument('--controls-log', default='cell-operations-review-controls-1.log')
parser.add_argument('--assembly-log', default='cell-operations-review-assembly-1.log')
parser.add_argument('--integration-log', default='cell-operations-review-integration-1.log')
parser.add_argument('--check-trial', type=int, default=1)
parser.add_argument('--artifact', action='append', default=[])
args = parser.parse_args()
ROOT = Path.cwd()
TASK = args.task_dir
OUT = ROOT / 'reports/data/hexrcf-cell-operations'
BASE = OUT / 'context.json'
SOURCE = args.source
baseline = json.loads(BASE.read_text())
sha = lambda raw: hashlib.sha256(raw).hexdigest()


def blob(commit, name):
    return subprocess.check_output(['git', 'show', commit + ':' + name], stderr=subprocess.DEVNULL)


sources = {}
for name in baseline['sources_sha256']:
    raw = blob(SOURCE, name)
    assert raw == (ROOT / name).read_bytes(), name
    sources[name] = sha(raw)
manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
assert sources[manual] == baseline['sources_sha256'][manual]
selection = {'controls': args.controls_log, 'assembly': args.assembly_log,
             'integration': args.integration_log}
for name, path in selection.items():
    raw = (TASK / path).read_bytes()
    assert b'status=0/SUCCESS' in raw and b'Build completed successfully' in raw, name
    if name != 'controls':
        assert b'fresh original real goal proved from actual reached-record assembly' in raw, name
    if name == 'integration':
        assert b'fresh ordinary-kernel real witness checked from actual record assembly' in raw, name
for name in ['dag', 'admissions', 'copyright']:
    assert b'exit_status=0' in (TASK / f'cell-operations-review-{name}-{args.check_trial}.log').read_bytes()
logs = {}
for path in sorted(TASK.glob('cell-operations-review-*.log')):
    raw = path.read_bytes()
    dest = OUT / (path.name + '.gz')
    dest.write_bytes(gzip.compress(raw, mtime=0))
    logs[str(dest.relative_to(ROOT))] = {
        'sha256': sha(dest.read_bytes()), 'uncompressed_sha256': sha(raw)}
artifacts = {}
for name in ['cell-operations-review-assembly-1.events',
             'cell-operations-review-live-limits.properties'] + args.artifact:
    raw = (TASK / name).read_bytes()
    (OUT / name).write_bytes(raw)
    artifacts[str((OUT / name).relative_to(ROOT))] = sha(raw)
props = (TASK / 'cell-operations-review-live-limits.properties').read_text()
assert all(value in props for value in
           ['ActiveState=active', 'MemoryMax=34359738368', 'MemorySwapMax=0'])
record = {
    'source_commit': SOURCE, 'sources_sha256': sources,
    'baseline_record': str(BASE.relative_to(ROOT)), 'baseline_record_sha256': sha(BASE.read_bytes()),
    'logs': logs, 'artifacts_sha256': artifacts,
    'current_selection': selection,
    'other_logs_scope': 'Prior-source or narrower validations; source scopes are retained in the preceding records.',
    'validation': {
        'source_and_fresh_consumer_completion': True,
        'exact_rejection_diagnostics_and_state_restoration': True,
        'required_record_law': 'Hex.RealClosure.Algebraic.Element.replayMul_eq',
        'shared_fixture_dictionary_source_acceptance_and_producer_exclusions': True,
        'direct_checked_body_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'manual_source_unchanged': True, 'memory_bytes': 34359738368, 'swap_bytes': 0,
        'lean_threads': 2, 'own_build_concurrency': 1},
    'limits': baseline['limits'],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-cell-operations.md',
             'reports/data/hexrcf-cell-operations/collect_controls.py']
try:
    current = {p: blob(head, p) for p in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    current = {}
if current and all(current[p] == (ROOT / p).read_bytes() for p in current):
    record['document_commit'] = head
    record['artifact_commit'] = head
    record['documents_sha256'] = {p: sha(current[p]) for p in documents}
(OUT / args.record).write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(sources), 'sources;', len(logs), 'logs;', len(artifacts), 'artifacts')
