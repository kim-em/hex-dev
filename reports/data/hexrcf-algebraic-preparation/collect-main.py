#!/usr/bin/env python3
"""Retain the expanded validation against landed owner and library changes."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-algebraic-preparation'
SOURCE = 'e9b99f9f9fb8ffdd03f67a6b29979e13d5caad1c'
UPSTREAM = subprocess.check_output(['git', 'rev-parse', SOURCE + '^2'], text=True).strip()
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'conformance/HexRCF/AlgebraicPreparationConformance.lean',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean', 'HexRCF/README.md',
    'lakefile.lean', 'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
    'adapters/HexRealClosureTheory/FiniteData.lean', 'libraries.yml',
    'HexSignDet/Codec.lean', 'HexSignDet/DagEncode.lean',
    'lake-manifest.json', 'lean-toolchain',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


for path in SOURCES:
    assert source(SOURCE, path) == (ROOT / path).read_bytes(), path
subprocess.run(['git', 'diff', '--quiet', UPSTREAM, SOURCE, '--',
                'AGENTS.md', 'PLAN.md', 'SPEC', '.github', 'HexRealClosure',
                'HexRealClosureTheory', 'HexSignDet', 'HexSignDetTheory'], check=True)
logs = {}
for path in sorted(SCRATCH.glob('algebraic-preparation-main-*-1.log')):
    raw = path.read_bytes()
    if path.name == 'algebraic-preparation-main-integration-1.log':
        assert b'Build completed successfully (14300 jobs)' in raw
        assert b'status=0/SUCCESS' in raw
        assert b'fresh complete-packet source body rechecked' in raw
        assert b'fresh Boolean source body rechecked' in raw
    else:
        assert b'exit_status=0' in raw, path
    destination = OUT / (path.name + '.gz')
    destination.write_bytes(gzip.compress(raw, mtime=0))
    logs[destination.relative_to(ROOT).as_posix()] = {
        'sha256': digest(destination.read_bytes()), 'uncompressed_sha256': digest(raw)}
assert len(logs) == 7
record = {
    'source_commit': SOURCE, 'upstream_commit': UPSTREAM,
    'sources_sha256': {p: digest(source(SOURCE, p)) for p in SOURCES},
    'logs': logs, 'artifacts_sha256': {},
    'validation': {'selected_jobs': 14300, 'admission_cones': 650, 'admission_modules': 1550,
        'admission_unit_tests': 11, 'dag_unit_tests': 11,
        'protected_or_owner_diff': [], 'memory_bytes': 34359738368,
        'swap_bytes': 0, 'lean_threads': 2, 'own_build_concurrency': 1},
    'limits': ['This integration has a distinct incremental scope and is not a timing comparison.',
        'The earlier source, checkpoint, render and probe records retain their own exact versions.',
        'No general frozen history or strict arbitrary-missing-record compiled replay is established.'],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-preparation.md',
             'reports/data/hexrcf-algebraic-preparation/collect-main.py']
try:
    tracked = {p: source(head, p) for p in documents + list(logs)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[p] == (ROOT / p).read_bytes() for p in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {p: digest(tracked[p]) for p in documents}
    record['artifact_commit'] = head
(OUT / 'main-context.json').write_text(json.dumps(record, indent=2) + '\n')
print(SOURCE, len(SOURCES), 'sources;', len(logs), 'successful logs')
