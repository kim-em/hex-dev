#!/usr/bin/env python3
"""Build a fresh Mathlib-free ECPP client with coordinated source prerequisites."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

import yaml

import sync_released as sync

ROOT = Path(__file__).resolve().parents[2]
LIBRARIES = {"HexBasic": [], "HexArith": [],
             "HexPrimality": ["HexBasic", "HexArith"],
             "HexECPP": ["HexArith", "HexPrimality"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.directory.exists() or args.output.exists():
        parser.error("use fresh paths; preserve previous evidence")
    args.directory.mkdir(parents=True)
    entries = {e["lib"]: e for e in yaml.safe_load(sync.MANIFEST.read_text())["repos"]
               if e.get("lib") in LIBRARIES}
    entries.setdefault("HexECPP", dict(repo="leanprover/hex-ecpp", lib="HexECPP",
                                      umbrella=True, spec="hex-ecpp", lakefile="toml"))
    for lib, deps in LIBRARIES.items():
        dest = args.directory / lib
        dest.mkdir()
        shutil.copy(ROOT / "lean-toolchain", dest)
        if lib == "HexArith":
            source = (ROOT / "lakefile.lean").read_text()
            blocks = "\n\n".join(source[a:b].rstrip() for a, b in
                                   (sync.lake_declaration(source, n) for n in
                                    ["hexArithOTarget", "hexarithffi"]))
            (dest / "lakefile.lean").write_text(
                'import Lake\nopen System Lake DSL\npackage «hex-arith» where\n'
                '  leanOptions := #[⟨`doc.verso, true⟩, ⟨`doc.verso.suggestions, false⟩]\n\n'
                + blocks + '\n\n@[default_target]\nlean_lib HexArith where\n'
                '  precompileModules := true\n  moreLinkArgs := #["-lgmp"]\n'
                '  moreLinkObjs := #[hexarithffi]\n')
        else:
            text = (f'name = "{entries[lib]["repo"].split("/")[-1]}"\n'
                    f'defaultTargets = ["{lib}"]\n\n'
                    'leanOptions = [{ name = "doc.verso", value = true },\n'
                    '  { name = "doc.verso.suggestions", value = false }]\n')
            for dep in deps:
                text += f'\n[[require]]\nname = "{dep}"\npath = "../{dep}"\n'
            text += f'\n[[lean_lib]]\nname = "{lib}"\n'
            (dest / "lakefile.toml").write_text(text)
        sync.apply_paths(entries[lib], dest)
        sync.rewrite_lib_settings(entries[lib], dest)
    client = args.directory / "Client"
    client.mkdir()
    shutil.copy(ROOT / "lean-toolchain", client)
    (client / "lakefile.toml").write_text(
        'name = "ecpp-client"\ndefaultTargets = ["Quickstart"]\n'
        '[[require]]\nname = "HexECPP"\npath = "../HexECPP"\n'
        '[[lean_lib]]\nname = "Quickstart"\n')
    code = re.search(r"```lean\n(.*?)\n```", (ROOT / "HexECPP/README.md").read_text(), re.S)[1]
    (client / "Quickstart.lean").write_text(code + "\n")
    command = ["lake", "build"]
    result = subprocess.run(command, cwd=client, capture_output=True, text=True)
    sources = {str(p.relative_to(args.directory)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in args.directory.rglob("*") if p.is_file() and
               ".lake" not in p.relative_to(args.directory).parts}
    forbidden = [str(p) for p in args.directory.rglob("*")
                 if p.is_dir() and p.name.lower() == "mathlib"]
    record = dict(source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                                 text=True).strip(),
                  command=command, cwd=str(client), returncode=result.returncode,
                  stdout=result.stdout, stderr=result.stderr, source_hashes=sources,
                  mathlib_directories=forbidden,
                  contract="Coordinated next-release sources, local paths for exact staged "
                           "prerequisites; a fresh client uses the README verbatim. Lake "
                           "generates all lockfiles. No development project cache is reused.")
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode or forbidden:
        raise SystemExit(result.stdout + result.stderr + str(forbidden))
    print("Fresh ECPP split and README client passed without Mathlib")


if __name__ == "__main__":
    main()
