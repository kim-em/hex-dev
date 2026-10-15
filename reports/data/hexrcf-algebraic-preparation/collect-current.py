#!/usr/bin/env python3
"""Retain checkpoint integration and public-module API probes separately."""
from pathlib import Path
import gzip
import hashlib
import json
import shutil
import subprocess

ROOT = Path.cwd()
SCRATCH = Path('/home/kim/.codex/tasks/hex-10358')
OUT = ROOT / 'reports/data/hexrcf-algebraic-preparation'
SOURCE = '6db3d5f7cd4f9cf9c52b6f11c0838d17b58fbb1c'
RENDER = '694e85356ca2d19eaadb15ae87130dbc1791ca4b'
OWNER = '82d5a6e0359b8502bf53b6bed62628ffae02a387'
SOURCES = [
    'adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean',
    'adapters/HexRCF/RealCoefficients.lean',
    'conformance/HexRCF/AlgebraicPreparationConformance.lean',
    'HexManual/Chapters/HexRCF/AlgebraicCells.lean',
    'HexRCF/README.md', 'lakefile.lean',
    'scripts/ci/check_named_admissions.py',
    'scripts/ci/test_check_named_admissions.py',
]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def source(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], stderr=subprocess.DEVNULL)


subprocess.run(['git', 'diff', '--quiet', SOURCE, '--', '.', ':!reports'], check=True)
manual = 'HexManual/Chapters/HexRCF/AlgebraicCells.lean'
assert source(SOURCE, manual) == source(RENDER, manual)
for name, needle in [
    ('algebraic-preparation-affected-7.log', b'Build completed successfully (14296 jobs)'),
    ('codec-exposure-control-1.log', b'Build completed successfully (11133 jobs)'),
]:
    raw = (SCRATCH / name).read_bytes()
    assert needle in raw and b'status=0/SUCCESS' in raw, name
public_failure = (SCRATCH / 'cell-operations-probe-2.log').read_bytes()
assert b'Tactic `decide` failed to reduce' in public_failure and b'Codec.readGraph' in public_failure
factory_failure = (SCRATCH / 'native-source-chain-2.log').read_bytes()
assert b'timeout at `isDefEq`' in factory_failure and b'(2400000)' in factory_failure
logs = {}
for name in ['algebraic-preparation-affected-6.log', 'algebraic-preparation-affected-7.log',
             'native-source-chain-1.log', 'native-source-chain-2.log',
             'cell-operations-probe-1.log', 'cell-operations-probe-2.log',
             'codec-exposure-control-1.log']:
    raw = (SCRATCH / name).read_bytes()
    destination = OUT / (name + '.gz')
    destination.write_bytes(gzip.compress(raw, mtime=0))
    logs[destination.relative_to(ROOT).as_posix()] = {
        'sha256': digest(destination.read_bytes()), 'uncompressed_sha256': digest(raw)}
artifacts = {}


def retain(path, name):
    destination = OUT / name
    shutil.copyfile(path, destination)
    artifacts[destination.relative_to(ROOT).as_posix()] = digest(destination.read_bytes())


retain(SCRATCH / 'native-source-chain-2-source.lean', 'native-source-chain-2.lean.txt')
retain(SCRATCH / 'native-source-chain.events', 'native-source-chain.events')
for name in ['CodecExposure', 'CodecExposedControl', 'CellWith']:
    retain(SCRATCH / 'boolean-render' / (name + '.lean'), name + '.lean.txt')
record = {
    'source_commit': SOURCE,
    'sources_sha256': {p: digest(source(SOURCE, p)) for p in SOURCES},
    'render_source_commit': RENDER,
    'render_sources_sha256': {manual: digest(source(RENDER, manual))},
    'owner_source_commit': OWNER,
    'owner_sources_sha256': {p: digest(source(OWNER, p)) for p in
        ['HexSignDet/Codec.lean', 'HexSignDet/Codec/Basic.lean']},
    'factory_source_commit': RENDER,
    'factory_sources_sha256': {p: digest(source(RENDER, p)) for p in
        ['adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean',
         'adapters/HexRealClosureTheory/FiniteChain.lean',
         'HexRealClosure/NumberFieldTower.lean']},
    'logs': logs,
    'artifacts_sha256': artifacts,
    'validation': {
        'complete_manual_jobs': 14296,
        'public_codec_reduction': 'failed: readGraph body unavailable',
        'private_body_control_jobs': 11133,
        'native_factory_extraction': 'isDefEq heartbeat exhaustion at 2400000',
        'memory_bytes': 34359738368, 'swap_bytes': 0,
        'own_build_concurrency': 1, 'lean_threads': 2,
    },
    'limits': [
        'The earlier context remains the separate record for its source and rendered manual.',
        'The displayed chapter is byte-identical across render and checkpoint implementation sources.',
        'Interruptions are observed before and after native calls, not inside their execution.',
        'The public-module probe is malformed rational graph rejection, not full complete-packet acceptance.',
        'The private import is a diagnostic control only, not an adapter import or production workaround.',
        'Factory-context extraction exhaustion is an operational limitation, not evidence of a missing mathematical theorem.',
        'The CellWith prototype proves only specialization/radical operation equalities, not full operation-parametric replay.',
    ],
}
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
documents = ['reports/hexrcf-algebraic-preparation.md',
             'reports/data/hexrcf-algebraic-preparation/collect-current.py']
try:
    tracked = {p: source(head, p) for p in documents + list(logs) + list(artifacts)}
except subprocess.CalledProcessError:
    tracked = {}
if tracked and all(tracked[p] == (ROOT / p).read_bytes() for p in tracked):
    record['document_commit'] = head
    record['documents_sha256'] = {p: digest(tracked[p]) for p in documents}
    record['artifact_commit'] = head
(OUT / 'checkpoint-context.json').write_text(json.dumps(record, indent=2) + '\n')
print('Retained checkpoint source', SOURCE, 'and', len(logs), 'logs')
