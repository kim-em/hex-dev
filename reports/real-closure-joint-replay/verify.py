#!/usr/bin/env python3
"""Verify the terminal current-main fixture; archive its actual compiler inputs.

This is a fixed-fixture acceptance check, not completion of issue #10378.
It never invokes Lean, changes source, or accepts a running/failed build.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil

TASK = Path(__file__).resolve().parent
WORK = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10378-public-main')
ORIGINAL = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10378-guard131-capture')
TARGET = 'KernelReplay.GuardJointPublicAudit'
CORE = ['GuardJoint', 'GuardJointAudit', 'GuardJointExport', 'GuardJointPublic', 'GuardJointUse', 'GuardJointPublicAudit', 'FramePublic']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    value = hashlib.sha256()
    with path.open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            value.update(chunk)
    return value.hexdigest()


def flatten(value):
    if isinstance(value, str):
        yield Path(value)
    elif isinstance(value, list):
        for child in value:
            yield from flatten(child)


def once(log, pattern, label):
    matches = re.findall(pattern, log)
    require(len(matches) == 1, f'Expected exactly one {label}, found {len(matches)}.')
    return matches[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', default='public-joint-main-v10-evidence')
    parser.add_argument('--output', default='public-joint-main-v6-accepted')
    args = parser.parse_args()
    evidence, output = TASK / args.evidence, TASK / args.output
    require(evidence.parent == TASK and output.parent == TASK, 'Expected task-local directory names.')
    require((evidence / 'result.json').is_file(), 'No terminal archived result; keep the same build running.')
    result = json.loads((evidence / 'result.json').read_text())
    require(result['target'] == TARGET, 'Wrong audit target.')
    require(result['exit_code'] == result['verification_exit_code'] == 0, 'Build/archive verification failed.')
    require(result['source_immutable_verified'] and result['accepted_original_inputs_verified'] == 1240,
            'Immutable source/frozen original verification failed.')
    require(result['compiled_target_olean_archived'], 'Actual target compiler artifact was not archived.')
    require(result.get('lake_build_completed') is True and
            result.get('process_killed_or_dumped') is False, 'No normal completed build.')
    require(not (evidence / 'acceptance-rejection.json').exists(), 'This run was explicitly rejected.')
    require(not output.exists(), 'Refusing to overwrite an acceptance archive.')
    snapshot = json.loads((evidence / 'source.json').read_text())
    require(snapshot['worktree'] == str(WORK) and snapshot['target'] == TARGET, 'Wrong source provenance.')
    for name, sha in snapshot['hashes'].items():
        require(digest(WORK / name) == sha == digest(evidence / 'sources' / name), f'Source differs: {name}')
    current = set()
    for directory, children, names in os.walk(WORK, followlinks=False):
        children[:] = [name for name in children if name not in {'.git', '.lake', '__pycache__', 'node_modules'}]
        for name in names:
            if name.endswith('.lean') or name in {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}:
                current.add(str((Path(directory) / name).relative_to(WORK)))
    require(not current.difference(snapshot['hashes']), 'New live source/config input appeared.')
    for name, sha in snapshot['tool_hashes'].items():
        require(digest(Path(name)) == sha, f'Build tool differs: {name}')
    frozen = json.loads((TASK / 'original-joint-v3-evidence/source.json').read_text())['hashes']
    require(len(frozen) == 1240, 'Wrong frozen original input count.')
    for name, sha in frozen.items():
        require(digest(ORIGINAL / name) == sha, f'Frozen original differs: {name}')
    prior = json.loads((TASK / 'public-joint-consumer-v1-accepted/accepted.json').read_text())
    log = (evidence / 'build.log').read_text()
    pins = json.loads((TASK / 'public-joint-interface-v6-pins.json').read_text())
    for name, sha in pins.items():
        require(snapshot['hashes'][name] == sha, f'Pinned checked source changed: {name}')
    for module in ['GuardJoint', 'GuardJointAudit']:
        name = f'experiments/KernelReplay/{module}.lean'
        require(snapshot['hashes'][name] == prior['source_sha256'][name],
                f'Original checked constructor/audit changed: {module}')
    for module in CORE:
        name = f'experiments/KernelReplay/{module}.lean'
        require(snapshot['hashes'][name] == pins[name], f'Reviewed interface source changed: {module}')
        source = (WORK / name).read_text()
        require(bool(re.search(r'^module$', source, re.M)) == (module not in ['GuardJointAudit', 'GuardJointPublicAudit']),
                f'Normal-module/full-body audit boundary changed: {module}')
    client = (WORK / 'experiments/KernelReplay/GuardJointUse.lean').read_text()
    require('public import KernelReplay.GuardJointPublic' in client and 'import all' not in client,
            'Witness extraction is not through the ordinary public interface.')
    require('rcases GuardJointPublic.exists_points' in client,
            'Ordinary client does not extract the actual theorem witnesses.')
    require(re.search(r'(?:Built|Replayed) KernelReplay.GuardJointUse', log),
            'Ordinary module consumer was not built/replayed successfully.')
    require(re.findall(r'^public import (\S+)$', client, re.M) == ['KernelReplay.GuardJointPublic'],
            'Client needs an additional explicit import beyond the public joint entrypoint.')
    require('theorem coordinates' in client and '#print axioms coordinates' in client,
            'Missing ordinary-client root/product theorem or its axiom guard.')
    export_source = (WORK / 'experiments/KernelReplay/GuardJointExport.lean').read_text()
    require('set_option Elab.async false' in export_source and
            'set_option debug.skipKernelTC false' in export_source,
            'Export does not explicitly check declarations synchronously.')
    export_hb = once(log, r'joint export checked: aggregateHeartbeat=(\d+)', 'synchronous checked export')
    require(0 < int(export_hb) <= 1500000, 'Joint export exceeded the aggregate budget.')
    client_setup = json.loads((WORK / '.lake/build/ir/KernelReplay/GuardJointUse.setup.json').read_text())
    require(client_setup['name'] == 'KernelReplay.GuardJointUse' and client_setup['isModule'],
            'Witness extraction did not use an ordinary module compilation.')
    audit_source = (WORK / 'experiments/KernelReplay/GuardJointPublicAudit.lean').read_text()
    require('let originals := GuardFrontier.templates.getState' in audit_source and
            'let mut expected := originals[index]!' in audit_source,
            'Guard statement check does not use raw original discovery templates.')
    dependency_source = (WORK / 'experiments/KernelReplay/GuardDependencyAudit.lean').read_text()
    require('env.getModuleIdxFor? name == some cachedModule' in dependency_source and
            'checked.find? name' in dependency_source and '.opaqueInfo value' in dependency_source,
            'Actual checked-body/module-origin audit changed.')
    controls = once(log, r'cached operand controls: directType=true proofBody=true privateRecords=(\d+) genericConstant=true',
                    'cached module controls')
    bindings = once(log, r'public cached operand negative control: rejected=true originalBindings=(\d+)',
                    'original native binding control')
    require(int(controls) > 0 and int(bindings) > 0, 'No actual private cached records/bindings inspected.')
    codec_evidence = TASK / 'signature-codec-public-v3-evidence'
    codec_result = json.loads((codec_evidence / 'result.json').read_text())
    codec_snapshot = json.loads((codec_evidence / 'source.json').read_text())
    require(codec_result['exit_code'] == codec_result['verification_exit_code'] == 0 and
            codec_result['source_immutable_verified'] and codec_result.get('lake_build_completed') is True and
            codec_result.get('process_killed_or_dumped') is False and
            codec_result['accepted_original_inputs_verified'] == 1240,
            'Public full-signature consumer did not pass its checked build.')
    for name in ['HexRealClosure/TowerContext.lean', 'HexRealClosure/SignatureCodecTests.lean']:
        require(codec_snapshot['hashes'][name] == snapshot['hashes'][name] ==
                digest(codec_evidence / 'sources' / name), f'Codec owner/client source changed: {name}')
    require(codec_snapshot['tool_hashes'] == snapshot['tool_hashes'], 'Codec build runner changed.')
    for name, sha in codec_result['artifacts'].items():
        require(digest(WORK / name) == sha == digest(codec_evidence / 'artifacts' / name),
                f'Codec consumer artifact changed: {name}')
    codec_setup = json.loads((WORK / '.lake/build/ir/HexRealClosure/SignatureCodecTests.setup.json').read_text())
    require(codec_setup['isModule'], 'Codec consumer was not compiled as an ordinary module.')
    for name, sha in result['artifacts'].items():
        require(digest(WORK / name) == sha == digest(evidence / 'artifacts' / name), f'Target artifact differs: {name}')
    log = (evidence / 'build.log').read_text()
    require(re.search(r'Build completed successfully \(\d+ jobs\)\.', log), 'No complete successful build marker.')
    construction = once(log, r'original joint construction result: witnesses=3 originalGuards=3773 completeClauses=3778 fullOrderedBaseAgreement=true inheritedProviderValuesFixed=true bothOriginalInventories=true originalNativeProduct=true chosenWitnessesAbsentFromStatement=true dependencyAuditPending=true aggregateHeartbeat=(\d+)', 'complete original constructor')
    statement = once(log, r'public joint statement audit: witnesses=3 originalGuards=3773 completeClauses=3778 completeOriginalAlias=true fullOrderedBaseAgreement=true inheritedProviderValuesFixed=true bothOriginalInventories=true allGuardClausesAtSharedReaders=true originalNativeProduct=true chosenWitnessesAbsentFromStatement=true aggregateHeartbeat=(\d+)', 'exact semantic statement audit')
    bodies = once(log, r'public joint full body audit: ordinaryPublicImports=true witnesses=3 originalGuards=3773 completeClauses=3778 exactStandardAxioms=true wholeFieldReferences=\[\] declarations=(\d+) aggregateHeartbeat=(\d+)', 'full private/opaque-body audit')
    require(int(bodies[0]) > 0, 'No checked declaration bodies.')
    for heartbeat in [construction, statement, bodies[1]]:
        require(0 < int(heartbeat) <= 1500000, 'New joint checked command exceeded its unchanged aggregate budget.')
    setup_path = WORK / '.lake/build/ir/KernelReplay/GuardJointPublicAudit.setup.json'
    setup = json.loads(setup_path.read_text())
    require(setup['name'] == TARGET and not setup['isModule'], 'Final audit compiler setup is not NONMODULE.')
    paths = {setup_path, WORK / '.lake/build/ir/HexRealClosure/SignatureCodecTests.setup.json'}
    for folder in ['lib/lean/HexRealClosure', 'ir/HexRealClosure']:
        paths.update(path for path in (WORK / '.lake/build' / folder).glob('SignatureCodecTests.*') if path.is_file())
    modules = set(CORE)
    external = set()
    for name, artifacts in setup['importArts'].items():
        for path in flatten(artifacts):
            require(path.is_file(), f'Actual imported compiler artifact is missing: {path}')
            if path.is_relative_to(WORK / '.lake/build'):
                paths.add(path)
                if name.startswith('KernelReplay.'):
                    modules.add(name.split('.', 1)[1])
            else:
                external.add(path)
    # Retain the setup/trace and private compiler artifacts of every imported
    # local fixture module as well as the four final theorem/audit modules.
    for module in sorted(modules):
        for folder in ['lib/lean/KernelReplay', 'ir/KernelReplay']:
            paths.update(p for p in (WORK / '.lake/build' / folder).glob(module + '.*') if p.is_file())
        require((WORK / f'.lake/build/lib/lean/KernelReplay/{module}.olean').is_file(), f'No compiled fixture module: {module}')
    for entry in setup.get('plugins', []) + setup.get('dynlibs', []):
        path = Path(entry['path'] if isinstance(entry, dict) else entry)
        require(path.is_file(), f'Actual compiler dynamic input is missing: {path}')
        if path.is_relative_to(WORK / '.lake/build'):
            paths.add(path)
        else:
            external.add(path)
    # Check and hash all actual external compiler inputs. Package caches are
    # separately immutable; archive their provenance without copying the cache.
    external_hashes = {str(path): digest(path) for path in sorted(external)}
    output.mkdir()
    artifacts = {}
    for path in sorted(paths):
        name = str(path.relative_to(WORK))
        sha = digest(path)
        destination = output / 'artifacts' / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
        require(digest(destination) == sha == digest(path), f'Artifact changed during archive: {name}')
        artifacts[name] = sha
    record = {
        'scope': 'Exact original fixed joint fixture on integrated main; expected-proposition proof sharing, ordinary-module witness extraction/original defining equations/native product and independent NONMODULE semantic/full-body audits',
        'evidence': str(evidence), 'worktree': str(WORK), 'verifier_sha256': digest(Path(__file__)),
        'interface_pins_sha256': digest(TASK / 'public-joint-interface-v6-pins.json'),
        'ordinary_module_witness_extraction': True,
        'ordinary_module_original_root_and_product_equations': True,
        'export_heartbeats': int(export_hb),
        'source_snapshot_sha256': digest(evidence / 'source.json'), 'result_sha256': digest(evidence / 'result.json'),
        'sources_verified': len(snapshot['hashes']), 'tools_verified': len(snapshot['tool_hashes']), 'frozen_original_inputs_verified': len(frozen),
        'source_sha256': {name: snapshot['hashes'][name] for name in pins},
        'raw_discovery_templates_compared': True, 'module_origin_cached_operand_exclusion': True,
        'private_record_controls': int(controls), 'original_binding_controls': int(bindings),
        'proof_body_only_negative_control': True, 'generic_constructor_positive_control': True,
        'public_signature_codec_consumer': True, 'codec_evidence': str(codec_evidence),
        'artifacts': artifacts, 'fixture_modules_archived': sorted(modules),
        'external_compiler_inputs_sha256': external_hashes,
        'witnesses': 3, 'original_guards': 3773, 'complete_clauses': 3778,
        'construction_heartbeats': int(construction), 'independent_statement_audit_heartbeats': int(statement),
        'full_checked_body_declarations': int(bodies[0]), 'full_body_audit_heartbeats': int(bodies[1]),
        'standard_axioms': ['propext', 'Classical.choice', 'Quot.sound'], 'whole_field_references': [],
        'fixed_fixture_current_main_acceptance': True, 'general_exporter_complete': False,
        'general_realizeReplay_complete': False, 'strict_compiled_rejection_complete': False,
        'phase4_complete': False, 'review_ci_merge_complete': False, 'goal_complete_claim': False,
    }
    (output / 'accepted.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'accepted': True, 'fixture_modules_archived': len(modules), 'artifact_files': len(artifacts),
                      'checked_bodies': int(bodies[0]), 'goal_complete': False}))


if __name__ == '__main__':
    main()
