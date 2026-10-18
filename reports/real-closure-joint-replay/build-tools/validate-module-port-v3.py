#!/usr/bin/env python3
"""Archive one serial Lean module build with all local Lean/config sources."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

TASK = Path(__file__).resolve().parent
WORK = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10378-public-main')
ORIGINAL = Path('/home/kim/worktrees/hex-dev/hex-dev-issue-10378-guard131-capture')
CONFIG_NAMES = {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}
SKIP_DIRS = {'.git', '.lake', '__pycache__', 'node_modules'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def original_snapshot():
    return json.loads((TASK / 'original-joint-v3-evidence/source.json').read_text())['hashes']


def verify_original():
    hashes = original_snapshot()
    for name, sha in hashes.items():
        require(digest(ORIGINAL / name) == sha, f'Frozen original changed: {name}')
    return len(hashes)


def local_inputs():
    # Package source/build caches remain the separately managed immutable cache.
    # Read every local Lean source, including ignored/untracked source modules.
    files = set()
    for directory, children, names in os.walk(WORK, followlinks=False):
        children[:] = sorted(name for name in children if name not in SKIP_DIRS)
        for name in names:
            if name.endswith('.lean') or name in CONFIG_NAMES:
                path = Path(directory) / name
                require(path.is_file(), f'Local source is missing: {path}')
                files.add(str(path.relative_to(WORK)))
    # Preserve any non-Lean inputs already identified by the original run.
    for name in original_snapshot():
        if (WORK / name).is_file():
            files.add(name)
    return sorted(files)


def ensure_idle():
    # This checks the actual held flock, never a stale file's mere existence.
    with (TASK / 'limited-experiment.lock').open('r') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise RuntimeError('An experiment is live; resume its existing monitor.') from error
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def tool_inputs():
    return {str(path): digest(path) for path in [
        Path(__file__).resolve(), TASK / 'bin/run-limited-experiment', TASK / 'bin/lean-cc']}


def artifact_paths(target):
    module = Path(*target.split('.'))
    files = []
    for directory in ['lib/lean', 'ir']:
        parent = WORK / '.lake/build' / directory / module.parent
        files.extend(path for path in parent.glob(module.name + '.*') if path.is_file())
    return sorted(files)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + chr(10))


def build_outcome(log):
    completed = len(re.findall(r'^Build completed successfully \(\d+ jobs\)\.$', log, re.M)) == 1
    killed = bool(re.search(r'^Main processes terminated with: code=(?:killed|dumped),', log, re.M))
    return completed, killed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--source', required=True)
    parser.add_argument('--evidence')
    parser.add_argument('--inspect-inputs', action='store_true')
    args = parser.parse_args()
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', args.target),
            'Expected one Lean module target.')
    source = Path(args.source)
    require(not source.is_absolute() and '..' not in source.parts and source.suffix == '.lean',
            'Expected a local relative Lean source.')
    require(source.stem == args.target.split('.')[-1], 'Target/source module names differ.')
    files = local_inputs()
    require(str(source) in files, 'Requested source has not been installed; no build started.')
    count = verify_original()
    hashes = {name: digest(WORK / name) for name in files}
    tools = tool_inputs()
    if args.inspect_inputs:
        print(json.dumps({
            'build_launched': False, 'target': args.target, 'source': str(source),
            'local_input_count': len(hashes), 'original_inputs_verified': count,
            'covers_LiveRequest': 'HexRealClosure/LiveRequest.lean' in hashes,
            'covers_LiveContext': 'HexRealClosure/LiveContext.lean' in hashes,
            'artifact_module_path': str(Path(*args.target.split('.'))),
            'tool_input_count': len(tools),
        }))
        return 0
    require(args.evidence, 'An evidence directory name is required for a build.')
    out = TASK / args.evidence
    require(out.parent == TASK and out.name not in {'.', '..'}, 'Expected one evidence directory name.')
    # The actual limited wrapper holds this same lock for the whole process.
    # Check before creating evidence; the wrapper checks atomically at launch.
    ensure_idle()
    require(not out.exists(), 'Refusing to overwrite archived evidence.')
    out.mkdir()
    write_json(out / 'source.json', {
        'worktree': str(WORK), 'target': args.target, 'source': str(source),
        'hashes': hashes, 'tool_hashes': tools,
        'coverage': 'All local Lean/config files plus retained existing original non-Lean inputs; package cache separately immutable',
    })
    for name, sha in hashes.items():
        destination = out / 'sources' / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(WORK / name, destination)
        require(digest(destination) == sha, f'Source changed while archiving: {name}')
    environment = os.environ.copy()
    environment.update({
        'LEAN_CC': str(TASK / 'bin/lean-cc'),
        'LD_LIBRARY_PATH': '/nix/store/chqq8mpmpyfi9kgsngya71akv5xicn03-gcc-15.2.0-lib/lib',
        'HEX_NATIVE_ASSEMBLY_TRACE': str(out / 'trace.log'),
    })
    command = [str(TASK / 'bin/run-limited-experiment'), 'env', 'LEAN_NUM_THREADS=2',
               'lake', 'build', args.target]
    with (out / 'build.log').open('w') as log:
        code = subprocess.run(command, cwd=WORK, env=environment,
                              stdout=log, stderr=subprocess.STDOUT).returncode
    after = set(local_inputs())
    changes = [name for name, sha in hashes.items()
               if name not in after or digest(WORK / name) != sha]
    added = sorted(after - hashes.keys())
    changed_tools = [name for name, sha in tools.items() if digest(Path(name)) != sha]
    original_count = None
    original_error = None
    try:
        original_count = verify_original()
    except Exception as error:
        original_error = str(error)
    artifacts = {}
    for path in artifact_paths(args.target):
        name = str(path.relative_to(WORK))
        destination = out / 'artifacts' / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, destination)
        artifacts[name] = digest(path)
        require(digest(destination) == artifacts[name], f'Artifact changed while archiving: {name}')
    has_olean = any(name.endswith('.olean') for name in artifacts)
    immutable = not changes and not added and not changed_tools
    completed, killed = build_outcome((out / 'build.log').read_text())
    success = code == 0 and completed and not killed and immutable and original_count == count and has_olean
    result = {
        'exit_code': code, 'verification_exit_code': 0 if success else 1,
        'source_immutable_verified': immutable,
        'changed_sources': changes, 'added_sources': added, 'changed_tools': changed_tools,
        'accepted_original_inputs_verified': original_count,
        'original_input_error': original_error,
        'target': args.target, 'source': str(source), 'artifacts': artifacts,
        'compiled_target_olean_archived': has_olean,
        'lake_build_completed': completed, 'process_killed_or_dumped': killed,
        'mathematical_acceptance_claim': False, 'goal_complete_claim': False,
    }
    write_json(out / 'result.json', result)
    print(json.dumps({key: value for key, value in result.items() if key != 'artifacts'}), flush=True)
    return 0 if success else 1


if __name__ == '__main__':
    raise SystemExit(main())
