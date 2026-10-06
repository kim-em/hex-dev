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
from intfactor_prospective import ENTRY

ROOT = Path(__file__).resolve().parents[2]
LIBRARIES = {'HexBasic': [], 'HexArith': [],
             'HexPrimality': ['HexBasic', 'HexArith'],
             'HexECPP': ['HexArith', 'HexPrimality']}


def proof_client(directory: Path, record: dict, output: Path):
    """Fresh prospective companions; external proof dependencies use pinned local caches."""
    for lib, deps in [
            ('HexPrimalityMathlib', ['HexPrimality']),
            ('HexECPPMathlib', ['HexECPP', 'HexPrimalityMathlib']),
            ('HexIntFactorMathlib', ['HexIntFactor', 'HexECPPMathlib', 'HexPrimalityMathlib'])]:
        dest = directory / lib
        dest.mkdir()
        shutil.copytree(ROOT / lib, dest / lib)
        shutil.copy(ROOT / f'{lib}.lean', dest)
        shutil.copy(ROOT / 'lean-toolchain', dest)
        requirements = ''.join(f'require {d} from "../{d}"\n' for d in deps)
        requirements += f'require mathlib from "{(ROOT / ".lake/packages/mathlib").resolve()}"\n'
        if lib == 'HexECPPMathlib':
            requirements += f'require AINTLIB from "{(ROOT / ".lake/packages/AINTLIB").resolve()}"\n'
        (dest / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\n' +
            f'package {lib}\n' + requirements + f'lean_lib {lib}\n')
    client = directory / 'ProofClient'
    client.mkdir()
    shutil.copy(ROOT / 'lean-toolchain', client)
    (client / 'lakefile.lean').write_text('import Lake\nopen Lake DSL\npackage ProofClient\n'
        'require HexIntFactorMathlib from "../HexIntFactorMathlib"\n'
        '@[default_target] lean_lib Proof\n')
    (client / 'Proof.lean').write_text('module\n'
        'public import HexIntFactorMathlib.Mixed\npublic import HexIntFactor.Mixed.Frozen.Small\n'
        'public section\nexample (p : Nat) : (34 : Nat).factorization p =\n'
        '  (Hex.Nat.Mixed.Frozen.small.factors.find? fun e => e.prime == p).elim 0 (·.exponent) :=\n'
        '  Hex.Nat.Mixed.Frozen.small_checked.factorization_eq p\n'
        '#print axioms Hex.Nat.Mixed.CheckedFactorization.factorization_eq\n')
    result = subprocess.run(['lake', 'build'], cwd=client, text=True, capture_output=True,
        env=dict(os.environ, HEX_INT_FACTOR_GP='/no-gp-in-proof-client'))
    record['proof_client'] = dict(returncode=result.returncode, stdout=result.stdout, stderr=result.stderr,
        external_dependencies=['mathlib', 'AINTLIB'], prospective_companions=['HexPrimalityMathlib', 'HexECPPMathlib', 'HexIntFactorMathlib'])
    output.write_text(json.dumps(record, indent=2) + '\n')
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    if 'depends on axioms: [propext, Classical.choice, Quot.sound]' not in result.stdout:
        raise SystemExit('unexpected proof dependency audit')
    print('Fresh companion mixed correspondence passed with the intended proof closure')


def prospective_lakefile(source: str | None = None) -> str:
    """The prospective Lake file, shaped as a generated one would be.

    It builds the optional producer/export modules separately, carries this
    monorepo's build settings for the library, copies the entry's native
    `lake_declarations` verbatim (targets before the library, carrier libraries
    after it, as `sync_released.render_lakefile` orders them), and builds the
    entry's test modules.
    """
    if source is None:
        source = sync.LAKEFILE.read_text(encoding='utf-8')
    settings = ''.join(f'  {name} := {value}\n' for name, value in
                       sync.source_build_settings('HexIntFactor').items())
    tests = ', '.join(f'`{module}' for module in ENTRY['test_modules'])
    declarations = ENTRY.get('lake_declarations', [])
    carriers = [d for d in declarations if re.search(rf'(?m)^lean_lib {re.escape(d)}\b', source)]
    helpers = [d for d in declarations if d not in carriers]
    text = ('import Lake\nopen System Lake DSL\npackage HexIntFactor\n'
        'require HexPrimality from "../HexPrimality"\n'
        'require HexECPP from "../HexECPP"\n')
    text += ''.join('\n' + sync._lean_declaration_text(source, name) for name in helpers)
    text += ('\n@[default_target]\nlean_lib HexIntFactor where\n'
        '  globs := #[`HexIntFactor, `HexIntFactor.Pari, `HexIntFactor.Export, `HexIntFactor.Replay, `HexIntFactor.Mixed.Replay, `HexIntFactor.Mixed.Import, `HexIntFactor.Mixed.Pari, `HexIntFactor.Mixed.Export, `HexIntFactor.Mixed.Frozen.Small].map Glob.one\n'
        + settings)
    text += ''.join('\n' + sync._lean_declaration_text(source, name) for name in carriers)
    return text + f'\nlean_lib HexIntFactorTests where\n  globs := #[{tests}]\n'


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
    (dest / 'lakefile.lean').write_text(prospective_lakefile())
    with patch.object(sync, "apply_ci_workflow", return_value=[]):
        sync.apply_paths(ENTRY, dest)
    sync.rewrite_toolchains(dest)
    client = args.directory / 'Client'
    client.mkdir()
    shutil.copy(ROOT / 'lean-toolchain', client)
    (client / 'lakefile.toml').write_text('name = "factor-replay-client"\ndefaultTargets = ["Replay"]\n'
        '[[require]]\nname = "HexIntFactor"\npath = "../HexIntFactor"\n'
        '[[lean_lib]]\nname = "Replay"\n'
        '[[lean_lib]]\nname = "Admission"\n')
    (client / 'Replay.lean').write_text('module\n'
        'public import HexIntFactor.Frozen.Case3\npublic import HexIntFactor.Frozen.Case5\n'
        'public import HexIntFactor.Frozen.Partial12\n'
        'public import HexIntFactor.Mixed.Frozen.Small\n'
        'public import HexIntFactor.Mixed.Frozen.CaseA\n'
        'public import HexIntFactor.Mixed.Frozen.CaseB\n'
        'public import HexIntFactor.Mixed.Frozen.Partial\n'
        'public section\n'
        'example : Hex.Nat.checkFactorization Hex.IntFactorFrozen.case3 = true := by decide +kernel\n'
        'example : Hex.Nat.checkPartial Hex.IntFactorFrozen.case5 = true := by decide +kernel\n'
        'example : Hex.Nat.checkPartial Hex.IntFactorFrozen.partial12 = true := by decide +kernel\n'
        'example : Hex.Nat.Mixed.CheckedFactorization 34 := Hex.Nat.Mixed.Frozen.small_checked\n'
        '#print axioms Hex.Nat.Mixed.Frozen.small_checked\n'
        '#print axioms Hex.IntFactorFrozen.case3_checked\n')
    (client / 'Admission.lean').write_text('module\n'
        'public import HexIntFactor.Mixed.Export\npublic section\n'
        '#int_factor_mixed for 34 using ⟨34, [(2, 1, some (.legacy (.small 2))), '
        '(17, 1, some (.ecpp (.step 17 2 3 3 6 6 [10, 13, 3, 13] (.base (.small 11)))))]⟩\n')
    result = subprocess.run(['lake', 'build', 'Replay', '+Admission'], cwd=client, text=True, capture_output=True,
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
    proof_client(args.directory, record, args.output)


if __name__ == '__main__':
    main()
