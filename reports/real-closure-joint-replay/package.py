#!/usr/bin/env python3
"""Prepare a task-local publication bundle from a terminal verified full audit."""
import argparse
import fcntl
import gzip
import hashlib
import json
from pathlib import Path

TASK = Path(__file__).resolve().parent
WORK = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10378-public-main')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    require(path.is_file(), f'Missing required record: {path}')
    return json.loads(path.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence', default='public-joint-main-v11-evidence')
    parser.add_argument('--acceptance', default='public-joint-main-v7-accepted')
    parser.add_argument('--destination', default='public-joint-main-v7-publication')
    args = parser.parse_args()
    evidence, acceptance, destination = (TASK / x for x in
        [args.evidence, args.acceptance, args.destination])
    for path in [evidence, acceptance, destination]:
        require(path.parent == TASK, 'Expected a single task-local directory name.')
    require(not destination.exists(), 'Refusing to overwrite an existing bundle.')
    result = read(evidence / 'result.json')
    require(result['exit_code'] == result['verification_exit_code'] == 0 and
            result.get('lake_build_completed') is True and
            result.get('process_killed_or_dumped') is False,
            'No normal completed immutable build to publish.')
    require(result['source_immutable_verified'] and
            result['accepted_original_inputs_verified'] == 1240,
            'Build source/frozen-input verification did not pass.')
    log = (evidence / 'build.log').read_text()
    require(log.count('Build completed successfully (') == 1 and
            'Main processes terminated with: code=killed,' not in log and
            'Main processes terminated with: code=dumped,' not in log,
            'Build log does not establish normal success.')
    require(not (evidence / 'acceptance-rejection.json').exists(),
            'The run was explicitly rejected.')
    accepted = read(acceptance / 'accepted.json')
    require(accepted['evidence'] == str(evidence) and accepted['worktree'] == str(WORK),
            'Acceptance belongs to another run/worktree.')
    verifier = TASK / 'verify-joint-main-v6.py'
    pins = TASK / 'public-joint-interface-v6-pins.json'
    require(accepted['verifier_sha256'] == digest(verifier) and
            accepted['interface_pins_sha256'] == digest(pins),
            'Acceptance does not bind the exact current verifier and interface pins.')
    require(accepted['source_snapshot_sha256'] == digest(evidence / 'source.json') and
            accepted['result_sha256'] == digest(evidence / 'result.json'),
            'Acceptance does not bind these build records.')
    for key in ['fixed_fixture_current_main_acceptance', 'raw_discovery_templates_compared',
                'module_origin_cached_operand_exclusion', 'proof_body_only_negative_control',
                'generic_constructor_positive_control', 'public_signature_codec_consumer',
                'ordinary_module_original_root_and_product_equations']:
        require(accepted.get(key) is True, f'Missing accepted contract: {key}')
    require(accepted['private_record_controls'] > 0 and accepted['original_binding_controls'] > 0,
            'No accepted private-record/binding controls.')
    snapshot = read(evidence / 'source.json')
    for name, sha in snapshot['hashes'].items():
        require(digest(WORK / name) == sha == digest(evidence / 'sources' / name),
                f'Changed checked source: {name}')
    for name, sha in snapshot['tool_hashes'].items():
        require(digest(Path(name)) == sha, f'Changed runner input: {name}')
    require(read(pins) == accepted['source_sha256'], 'Published interface pins differ.')
    for name, sha in accepted['artifacts'].items():
        require(digest(acceptance / 'artifacts' / name) == sha,
                f'Changed accepted compiler artifact: {name}')
    # Check an actual held lock, not the existence of its file. Packaging never
    # edits compiler inputs, and the destination is outside the repository.
    with (TASK / 'limited-experiment.lock').open('r') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError('An experiment is live; do not package its artifacts yet.') from error
    codec = Path(accepted['codec_evidence'])
    codec_acceptance_path = TASK/'signature-codec-public-v1-accepted/accepted.json'
    codec_acceptance = read(codec_acceptance_path)
    require(codec_acceptance['source_snapshot_sha256'] == digest(codec/'source.json') and
            codec_acceptance['result_sha256'] == digest(codec/'result.json'),
            'Codec acceptance does not bind the included build records.')
    require(codec_acceptance['ordinary_module'] and
            codec_acceptance['mathlib_free_actual_imports'] and codec_acceptance['axiom_guards'] == 5,
            'Codec public-import/axiom acceptance is incomplete.')
    for name, sha in codec_acceptance['source_sha256'].items():
        require(snapshot['hashes'].get(name) == sha,
                f'Codec acceptance source differs from the full joint source snapshot: {name}')
    construction = TASK / 'public-joint-main-v10-evidence'
    construction_acceptance = TASK / 'public-joint-main-v6-accepted/accepted.json'
    construction_bundle = TASK / 'public-joint-main-v6-publication'
    previous = read(construction_acceptance)
    previous_manifest = read(construction_bundle / 'evidence.json')
    require(previous['fixed_fixture_current_main_acceptance'] and
            previous['module_origin_cached_operand_exclusion'],
            'The supporting construction cohort was not accepted.')
    require(previous['source_sha256'] == accepted['source_sha256'] and
            previous['verifier_sha256'] == accepted['verifier_sha256'] and
            previous['interface_pins_sha256'] == accepted['interface_pins_sha256'],
            'The construction and final audits do not bind the same reviewed interfaces/verifier.')
    previous_result = read(construction / 'result.json')
    require(previous_result['exit_code'] == previous_result['verification_exit_code'] == 0 and
            previous_result['lake_build_completed'] and
            not previous_result['process_killed_or_dumped'] and
            previous_result['source_immutable_verified'] and
            previous_result['accepted_original_inputs_verified'] == 1240,
            'No normal completed immutable supporting construction build.')
    require(not (construction / 'acceptance-rejection.json').exists(),
            'The supporting construction run was explicitly rejected.')
    require(previous['source_snapshot_sha256'] == digest(construction / 'source.json') and
            previous['result_sha256'] == digest(construction / 'result.json'),
            'The supporting construction acceptance has different build records.')
    require(read(construction / 'source.json')['tool_hashes'] == snapshot['tool_hashes'],
            'The construction and final checks used different build tools.')
    for original, published in [
            (construction_acceptance, 'acceptance.json.gz'),
            (construction / 'build.log', 'build.log.gz'),
            (construction / 'source.json', 'source.json.gz'),
            (construction / 'result.json', 'result.json')]:
        info = previous_manifest['files'][published]
        require(digest(construction_bundle / published) == info['sha256'] and
                digest(original) == info['uncompressed_sha256'],
                f'The retained construction publication differs: {published}')
    destination.mkdir()
    files = {}
    def retain(source, name, compressed=False):
        raw = source.read_bytes()
        data = gzip.compress(raw, mtime=0) if compressed else raw
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        files[name] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data),
                       'uncompressed_sha256': hashlib.sha256(raw).hexdigest()}
    for source, name, compressed in [
        (acceptance/'accepted.json', 'acceptance.json.gz', True),
        (evidence/'build.log', 'build.log.gz', True),
        (evidence/'source.json', 'source.json.gz', True),
        (evidence/'result.json', 'result.json', False),
        (pins, 'interface-pins.json', False),
        (verifier, 'verify.py', False),
        (Path(__file__), 'package.py', False),
        (TASK/'original-joint-v3-evidence/source.json', 'frozen-original-source.json.gz', True),
    ]:
        retain(source, name, compressed)
    for source, name, compressed in [
        (codec/'build.log', 'codec-build.log.gz', True),
        (codec/'source.json', 'codec-source.json.gz', True),
        (codec/'result.json', 'codec-result.json', False),
        (codec_acceptance_path, 'codec-acceptance.json.gz', True),
    ]:
        retain(source, name, compressed)
    for source, name, compressed in [
        (construction/'build.log', 'construction/build.log.gz', True),
        (construction/'source.json', 'construction/source.json.gz', True),
        (construction/'result.json', 'construction/result.json', False),
        (construction_acceptance, 'construction/acceptance.json.gz', True),
    ]:
        retain(source, name, compressed)
    for source in snapshot['tool_hashes']:
        retain(Path(source), 'build-tools/' + Path(source).name)
    prefixes = ['cached operand controls:', 'joint export checked:',
                'original joint construction result:', 'public joint statement audit:',
                'public joint full body audit:', 'public cached operand negative control:']
    marker_lines = []
    for prefix in prefixes:
        matches = [line for line in log.splitlines() if prefix in line]
        require(len(matches) == 1, f'Expected one successful marker: {prefix}')
        marker_lines.extend(matches)
    marker = destination/'audit-markers.txt'
    marker.write_text('\n'.join(marker_lines)+'\n')
    files['audit-markers.txt'] = {'sha256':digest(marker), 'bytes':marker.stat().st_size,
                                'uncompressed_sha256':digest(marker)}
    manifest = {key: value for key, value in accepted.items() if key not in
                {'artifacts', 'external_compiler_inputs_sha256'}}
    manifest.update({
        'command':['lake','build','KernelReplay.GuardJointPublicAudit'],
        'construction_evidence': {
            'build_log':'construction/build.log.gz',
            'source':'construction/source.json.gz',
            'result':'construction/result.json',
            'acceptance':'construction/acceptance.json.gz',
            'same_reviewed_interface_sources':True,
            'same_build_tools':True,
            'note':'The retained full construction run checked all producers. The final source cohort reuses unchanged producer artifacts and freshly rebuilds the ordinary public consumer and final audit after upstream integration.',
        },
        'aggregate_memory_bytes':8589934592,'swap_bytes':0,'lean_threads':2,
        'ordinary_real_points':2,'compiler_artifacts_archived':len(accepted['artifacts']),
        'external_compiler_inputs_hashed':len(accepted['external_compiler_inputs_sha256']),
        'files':files,
        'evidence_notes':'Acceptance ledger retains host-local paths and hashes of large compiler artifacts; these payloads and package caches are not bundled. verify.py is the exact host-local verifier, and build-tools contains the exact three runner inputs. The source hashes, frozen-original manifest, normal completion result and audit markers are included. Run the Lean command to reproduce mathematical checks.',
        'validation_coverage':'Full fixed fixture locally; shared helpers and small dependency controls in CI. Source scan covers all Guard-root import cones.',
        'issue_10378_complete':False,
    })
    (destination/'evidence.json').write_text(json.dumps(manifest,indent=2)+'\n')
    # Read the staged bytes back, including decompression, before reporting it.
    for name, info in files.items():
        target = destination/name
        require(digest(target) == info['sha256'], f'Bad bundle hash: {name}')
        raw = gzip.decompress(target.read_bytes()) if name.endswith('.gz') else target.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == info['uncompressed_sha256'],
                f'Bad decompressed bundle hash: {name}')
    print(json.dumps({'bundle':str(destination),'payloads':len(files),
                      'repository_modified':False,'issue_10378_complete':False}))


if __name__ == '__main__':
    main()
