#!/usr/bin/env python3
"""Collect existing original-input validation, retaining the interrupted stress run."""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-algebraic-input-cells'
SOURCE = '2878412c6a4fdfeecfc5a0e181f00885a60d6d34'
STRESS = 'd873312be6cfdb6dedcd786bc06023dac72bd999'
MANUAL = 'ed5ba66439a2eef3fd60c645c965ab97823abedf'
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicCells.lean',
    'conformance/HexRCF/AlgebraicCellsConformance.lean',
    'conformance/HexRCF/AlgebraicCellsStress.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'lakefile.lean',
    'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
    'scripts/check_dag.py',
    'scripts/libgraph.py',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'HexRCF/README.md',
    'lean-toolchain',
    'lake-manifest.json',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


for log, needle in [
    ('algebraic-cells-final-1.log', b'Build completed successfully (11767 jobs)'),
    ('algebraic-cells-manual-build-2.log', b'Build completed successfully (11658 jobs)'),
    ('algebraic-cells-manual-render-1.log', b'Build completed successfully (14296 jobs)'),
    ('algebraic-cells-manual-browser-1.log', b'Saved algebraic-cells desktop/narrow screenshots'),
]:
    raw = (SCRATCH / log).read_bytes()
    assert needle in raw and b'status=0/SUCCESS' in raw, log
interrupted = (SCRATCH / 'algebraic-cells-conformance-1.log').read_bytes()
assert b'code=killed, status=15/TERM' in interrupted
assert b'Build completed successfully' not in interrupted
manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
assert source(SOURCE, manual) == source(MANUAL, manual)
assert (ROOT / manual).read_bytes() == source(SOURCE, manual)
logs = {}
for pattern in ['algebraic-cells-*.log', 'gather-factory-api-*.log']:
    for path in sorted(SCRATCH.glob(pattern)):
        raw = path.read_bytes()
        destination = OUT / (path.name + '.gz')
        destination.write_bytes(gzip.compress(raw, mtime=0))
        logs[destination.relative_to(ROOT).as_posix()] = {
            'sha256': digest(destination.read_bytes()),
            'uncompressed_sha256': digest(raw),
        }
artifacts = {}


def retain(path, name=None):
    destination = OUT / (name or path.name)
    shutil.copyfile(path, destination)
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())


render = SCRATCH / 'boolean-render'
for path in sorted(render.glob('algebraic-cells-*.png')):
    retain(path)
retain(render / 'algebraic-cells-inspection.json')
retain(SCRATCH / 'algebraic-cells-browser.mjs')
retain(SCRATCH / 'algebraic-cells-interrupted-memory.txt')
retain(SCRATCH / 'bin/run-bounded')
retain(SCRATCH / 'bin/lake-bounded')
retain(render / 'GatherFactory.lean', 'GatherFactory-prototype.txt')
inspection = json.loads((render / 'algebraic-cells-inspection.json').read_text())
assert len(inspection) == 10
assert all(row['descendantOverflow'] == 0 for row in inspection)
assert all(row['targetScrollWidth'] <= row['targetWidth'] for row in inspection)
record = {
    'source_commit': SOURCE,
    'sources_sha256': {p: digest(source(SOURCE, p)) for p in SOURCES},
    'interrupted_source_commit': STRESS,
    'interrupted_sources_sha256': {p: digest(source(STRESS, p)) for p in SOURCES[:2]},
    'manual_source_commit': MANUAL,
    'manual_sources_sha256': {manual: digest(source(MANUAL, manual))},
    'logs': logs,
    'artifacts_sha256': artifacts,
    'rendered_html_sha256': digest((render / 'full-html/html-single/index.html').read_bytes()),
    'validation': {
        'actual_theorem_bodies': 11,
        'selected_proof_build_jobs': 11767,
        'new_manual_chapter_build_jobs': 11658,
        'renderer_build_jobs': 14296,
        'captures_opened': 10,
        'local_overflow_pixels': 0,
        'admission_scan_cones': 646,
        'admission_scan_modules': 1546,
        'admission_checker_unit_tests': 11,
        'dag_checker_unit_tests': 11,
        'memory_bytes': 34359738368,
        'swap_bytes': 0,
        'lean_threads': 2,
        'own_build_concurrency': 1,
    },
    'stress_result': {
        'status': 'operator-interrupted',
        'signal': 'TERM',
        'service_runtime_seconds': 753.377,
        'cpu_seconds': 751.616,
        'reported_memory_peak': '1.4G',
        'reported_swap_peak': '0B',
        'completed_timing': False,
        'recorded_verdict': None,
        'active_case': None,
        'active_producer_or_replay_phase': None,
        'stack_samples': 3,
    },
    'limits': [
        'The wrapper result success during operator stop is not a passing Lake build: the actual main process was killed by TERM.',
        'Lake buffers job output; no particular active stress case or phase is established.',
        'The changed routine predicate and retained stronger stress predicate are different inputs, not timing-comparison arms.',
        'The selected eleven-proof build predates the automatic-input manual addition; the new manual has its own chapter build and complete render.',
        'The prototype artifact is development context; the committed module and eleven actual audited bodies provide the ordinary-kernel result.',
        'No frozen histories, arbitrary missing-record strictness, primitive common-field certification, frontend accepted completeness or stress-case completion is inferred.',
        'These are Mathlib-facing build/test observations, not a Mathlib-free executable benchmark or scaling claim.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-input-cells.md',
             'reports/data/hexrcf-algebraic-input-cells/collect.py']
try:
    tracked = {path: source(head, path) for path in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[path] == (ROOT / path).read_bytes() for path in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {path: digest(tracked[path]) for path in documents}
    record['artifact_commit'] = head
(OUT / 'context.json').write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(SOURCES), 'sources;', len(logs), 'logs;', len(artifacts), 'artifacts')
