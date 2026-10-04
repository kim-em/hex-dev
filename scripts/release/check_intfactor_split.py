#!/usr/bin/env python3
"""Build a fresh computational factor-replay client from publication-shaped sources.

HexIntFactor is not yet registered for publication. Its skeleton is prospective;
its upstream prerequisites use the real published repositories and sync transformations.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import yaml
from unittest.mock import patch
import sync_released as sync

ROOT = Path(__file__).resolve().parents[2]
LIBRARIES = {'HexBasic': [], 'HexArith': [],
             'HexPrimality': ['HexBasic', 'HexArith']}
ENTRY = dict(repo='prospective/hex-int-factor', lib='HexIntFactor', umbrella=True, spec='hex-int-factor', lakefile='lean',
             build_modules=['HexIntFactor.Pari', 'HexIntFactor.Export', 'HexIntFactor.Replay'],
             test_modules=['HexIntFactor.ImportTests', 'HexIntFactor.PariTests',
                           'HexIntFactor.ExportTests'] + [f'HexIntFactor.Frozen.Case{i}' for i in range(7)] + ['HexIntFactor.Frozen.Partial12'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if args.directory.exists() or args.output.exists():
        parser.error('use fresh paths')
    args.directory.mkdir(parents=True)
    all_entries = yaml.safe_load(sync.MANIFEST.read_text())['repos']
    entries = {e['lib']: e for e in all_entries if e.get('lib') in LIBRARIES}
    pins = sync.external_pins()
    for lib, deps in LIBRARIES.items():
        dest = args.directory / lib
        subprocess.run(['git', 'clone', '--depth', '1',
                        f"https://github.com/{entries[lib]['repo']}.git", str(dest)], check=True)
        sync.apply_paths(entries[lib], dest)
        sync.write_lakefile(entries[lib], dest, all_entries, 'v0.0.0', {}, pins)
        sync.rewrite_toolchains(dest)
        if deps:
            lakefile = dest / 'lakefile.toml'
            pattern = r'(?ms)^\[\[require\]\]\s*\n(?P<body>.*?)(?=^\[|\Z)'
            def local_requirement(match):
                name = re.search(r'^name\s*=\s*"([^"\n]+)"', match['body'], re.M)[1]
                if name not in LIBRARIES:
                    raise RuntimeError(f'unexpected requirement {name}')
                return f'[[require]]\nname = "{name}"\npath = "../{name}"\n\n'
            text, count = re.subn(pattern, local_requirement, lakefile.read_text())
            assert count >= len(deps)
            lakefile.write_text(text)
        (dest / 'lake-manifest.json').unlink(missing_ok=True)
    dest = args.directory / 'HexIntFactor'
    dest.mkdir()
    shutil.copy(ROOT / "lean-toolchain", dest)
    # The prospective Lake file builds optional producer/export modules
    # separately, carries this monorepo's build settings for the library, and
    # builds the entry's test modules, as a generated one would.
    settings = ''.join(f'  {name} := {value}\n' for name, value in
                       sync.source_build_settings('HexIntFactor').items())
    tests = ', '.join(f'`{module}' for module in ENTRY['test_modules'])
    (dest / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage HexIntFactor\n'
        'require HexPrimality from "../HexPrimality"\n'
        '@[default_target]\nlean_lib HexIntFactor where\n'
        '  globs := #[`HexIntFactor, `HexIntFactor.Pari, `HexIntFactor.Export, `HexIntFactor.Replay].map Glob.one\n'
        + settings + f'\nlean_lib HexIntFactorTests where\n  globs := #[{tests}]\n')
    with patch.object(sync, "apply_ci_workflow", return_value=[]):
        sync.apply_paths(ENTRY, dest)
    sync.rewrite_toolchains(dest)
    client = args.directory / 'Client'
    client.mkdir()
    shutil.copy(ROOT / 'lean-toolchain', client)
    (client / 'lakefile.toml').write_text('name = "factor-replay-client"\ndefaultTargets = ["Replay"]\n'
        '[[require]]\nname = "HexIntFactor"\npath = "../HexIntFactor"\n'
        '[[lean_lib]]\nname = "Replay"\n')
    (client / 'Replay.lean').write_text('module\n'
        'public import HexIntFactor.Frozen.Case3\npublic import HexIntFactor.Frozen.Case5\n'
        'public import HexIntFactor.Frozen.Partial12\n'
        'public section\n'
        'example : Hex.Nat.checkFactorization Hex.IntFactorFrozen.case3 = true := by decide +kernel\n'
        'example : Hex.Nat.checkPartial Hex.IntFactorFrozen.case5 = true := by decide +kernel\n'
        'example : Hex.Nat.checkPartial Hex.IntFactorFrozen.partial12 = true := by decide +kernel\n'
        '#print axioms Hex.IntFactorFrozen.case3_checked\n')
    result = subprocess.run(['lake', 'build'], cwd=client, text=True, capture_output=True,
        env=dict(os.environ, HEX_INT_FACTOR_GP='/no-gp-in-split-client'))
    forbidden = [str(p) for p in args.directory.rglob('*') if p.is_dir() and p.name.lower() == 'mathlib']
    record = dict(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr,
        mathlib_directories=forbidden, prospective_entry=ENTRY,
        sources={str(p.relative_to(args.directory)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in args.directory.rglob('*.lean') if '.lake' not in p.parts and '.git' not in p.parts})
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode or forbidden:
        raise SystemExit(result.stdout + result.stderr + str(forbidden))
    print('Fresh computational factor replay passed without GP, search or Mathlib')


if __name__ == '__main__':
    main()
