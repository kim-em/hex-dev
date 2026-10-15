#!/usr/bin/env python3
"""Bind native source preparation and retained stage diagnostics to their sources."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-algebraic-preparation'
SOURCE = '694e85356ca2d19eaadb15ae87130dbc1791ca4b'
PROBE = 'fb8f4664979df08f4525aa6a4f25629645ea6481'
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'conformance/HexRCF/AlgebraicPreparationConformance.lean',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'HexRCF/README.md', 'lakefile.lean',
    'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
]
PROBE_SOURCES = [
    f'adapters/HexRCF/RealCoefficients/{name}.lean' for name in
    ['AlgebraicCells', 'GatherCells', 'RepresentationSpecialize',
     'CellDiscover', 'CellBuild', 'RootBuild', 'RadicalBuild', 'SectorRequest']
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


OUT.mkdir(parents=True, exist_ok=True)
subprocess.run(['git', 'diff', '--quiet', SOURCE, '--', '.', ':!reports'], check=True)
for path in SOURCES:
    assert source(SOURCE, path) == (ROOT / path).read_bytes(), path
affected = (SCRATCH / 'algebraic-preparation-affected-5.log').read_bytes()
assert b'Build completed successfully (11768 jobs)' in affected and b'status=0/SUCCESS' in affected
render = (SCRATCH / 'algebraic-preparation-manual-render-3.log').read_bytes()
assert b'Build completed successfully (' in render and b'status=0/SUCCESS' in render
render_jobs = int(re.search(rb'Build completed successfully \((\d+) jobs\)', render)[1])
for name in ['admission', 'dag']:
    raw = (SCRATCH / f'algebraic-preparation-{name}-tests-3.log').read_bytes()
    assert b'Ran 11 tests' in raw and b'\nOK\n' in raw, name
for name in ['dag', 'admissions', 'copyright', 'literals']:
    raw = (SCRATCH / f'algebraic-preparation-final-{name}.log').read_bytes()
    assert b'exit_status=0' in raw, name
for i in [2, 3]:
    raw = (SCRATCH / f'original-input-stages-{i}.log').read_bytes()
    assert b'code=killed, status=15/TERM' in raw
    assert b'Build completed successfully' not in raw

logs = {}
paths = sorted(SCRATCH.glob('algebraic-preparation-*.log'))
paths += [SCRATCH / f'original-input-stages-{i}.log' for i in [1, 2, 3]]
for path in paths:
    raw = path.read_bytes()
    destination = OUT / (path.name + '.gz')
    destination.write_bytes(gzip.compress(raw, mtime=0))
    logs[destination.relative_to(ROOT).as_posix()] = {
        'sha256': digest(destination.read_bytes()), 'uncompressed_sha256': digest(raw)}

artifacts = {}


def retain(path, name=None):
    destination = OUT / (name or path.name)
    shutil.copyfile(path, destination)
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())


for i in [1, 2, 3]:
    retain(SCRATCH / f'original-input-stages-{i}-source.lean', f'original-input-stages-{i}-source.lean.txt')
retain(SCRATCH / 'original-input-stages-2.events')
retain(SCRATCH / 'original-input-stages-3-current.events')
retain(SCRATCH / 'original-input-stages-3-current.properties')
retain(SCRATCH / 'algebraic-preparation-browser.mjs')
for path in sorted((SCRATCH / 'algebraic-preparation-overflow-1').iterdir()):
    retain(path, 'overflow-1-' + path.name)
for name in ['run-bounded', 'lake-bounded']:
    retain(SCRATCH / 'bin' / name)
render_dir = SCRATCH / 'boolean-render'
for path in sorted(render_dir.glob('algebraic-preparation-*.png')):
    retain(path)
retain(render_dir / 'algebraic-preparation-inspection.json')
inspection = json.loads((render_dir / 'algebraic-preparation-inspection.json').read_text())
assert len(inspection) == 6
assert all(row['descendantOverflow'] == 0 for row in inspection)
assert all(row['targetScrollWidth'] <= row['targetWidth'] for row in inspection)
events = (SCRATCH / 'original-input-stages-3-current.events').read_text()
assert 'radical reduction done: degree 4; complete root table begin' in events
assert 'carrier/full-root preparation done: 4 roots; sector requests begin' in events
assert 'sector requests done; cell rows begin' in events
assert 'cell rows done' not in events

record = {
    'source_commit': SOURCE,
    'sources_sha256': {p: digest(source(SOURCE, p)) for p in SOURCES},
    'probe_source_commit': PROBE,
    'probe_sources_sha256': {p: digest(source(PROBE, p)) for p in PROBE_SOURCES},
    'logs': logs,
    'artifacts_sha256': artifacts,
    'rendered_html_sha256': digest((render_dir / 'native-preparation-html/html-single/index.html').read_bytes()),
    'validation': {
        'affected_jobs': 11768, 'renderer_jobs': render_jobs,
        'admission_unit_tests': 11, 'dag_unit_tests': 11,
        'source_identity_allowed_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'captures_opened': 6, 'local_overflow_pixels': 0,
        'memory_bytes': 34359738368, 'swap_bytes': 0,
        'lean_threads': 2, 'own_build_concurrency': 1,
    },
    'limits': [
        'Source identities authenticate expressions, not separately quoted compiled proposals.',
        'No new tactic handler or general frozen-history acceptance is claimed.',
        'Earlier failed attempts remain raw diagnostic artifacts; validated current sources are distinguished.',
        'Both instrumented native stress runs were operator-interrupted, with no accepted verdict.',
        'The detailed trace identifies completed radical/root-table/sector work and entry to unfinished cell-row production, not a specific inner query.',
        'The build-only probes import Mathlib and are not executable benchmark evidence.',
        'Operational build observations with different scopes are not performance comparisons.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-preparation.md',
             'reports/data/hexrcf-algebraic-preparation/collect.py']
try:
    tracked = {p: source(head, p) for p in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[p] == (ROOT / p).read_bytes() for p in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {p: digest(tracked[p]) for p in documents}
    record['artifact_commit'] = head
(OUT / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(len(SOURCES), 'sources;', len(PROBE_SOURCES), 'probe sources;', len(logs), 'logs;', len(artifacts), 'artifacts')
