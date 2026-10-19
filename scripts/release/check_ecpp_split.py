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
    parser.add_argument("--native512-subject", type=int)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    if args.directory.exists() or args.output.exists():
        parser.error("use fresh paths; preserve previous evidence")
    args.directory.mkdir(parents=True)
    all_entries = yaml.safe_load(sync.MANIFEST.read_text())["repos"]
    entries = {e["lib"]: e for e in all_entries if e.get("lib") in LIBRARIES}
    pins = sync.external_pins()
    skeleton_heads = {}
    for lib, deps in LIBRARIES.items():
        dest = args.directory / lib
        subprocess.run(["git", "clone", "--depth", "1",
                        f"https://github.com/{entries[lib]['repo']}.git", str(dest)], check=True)
        skeleton_heads[lib] = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=dest, text=True).strip()
        # Apply the actual publication transformations, including the generated
        # Lake file, to the published repositories.
        sync.apply_paths(entries[lib], dest)
        sync.write_lakefile(entries[lib], dest, all_entries, "v0.0.0", {}, pins)
        sync.rewrite_toolchains(dest)
        lakefile = dest / f"lakefile.{entries[lib]['lakefile']}"
        if deps:
            text = lakefile.read_text()
            pattern = r'(?ms)^\[\[require\]\]\s*\n(?P<body>.*?)(?=^\[|\Z)'
            def local_requirement(match):
                name = re.search(r'^name\s*=\s*"([^"\n]+)"', match['body'], re.M)[1]
                if name not in LIBRARIES:
                    raise RuntimeError(f"unexpected dependency {name} in {lib}")
                return f'[[require]]\nname = "{name}"\npath = "../{name}"\n\n'
            text, count = re.subn(pattern, local_requirement, text)
            if count < len(deps):
                raise RuntimeError(f"missing direct requirement in {lib}")
            lakefile.write_text(text)
        (dest / "lake-manifest.json").unlink(missing_ok=True)
    client = args.directory / "Client"
    client.mkdir()
    shutil.copy(ROOT / "lean-toolchain", client)
    (client / "lakefile.toml").write_text(
        'name = "ecpp-client"\ndefaultTargets = ["Quickstart"]\n'
        '[[require]]\nname = "HexECPP"\npath = "../HexECPP"\n'
        '[[lean_lib]]\nname = "Quickstart"\n')
    code = re.search(r"```lean\n(.*?)\n```", (ROOT / "HexECPP/README.md").read_text(), re.S)[1]
    (client / "Quickstart.lean").write_text(code + "\n")
    if args.native512_subject is not None:
        if args.native512_subject.bit_length() != 512:
            parser.error("the extended split probe requires a 512-bit subject")
        with (client / "lakefile.toml").open("a") as handle:
            handle.write('\n[[lean_exe]]\nname = "native512"\nroot = "Native512"\n')
        (client / "Native512.lean").write_text(
            "import HexECPP\nopen Hex.ECPP\n"
            "def main : IO Unit := do\n"
            f"  let result := produce {args.native512_subject} {args.seed} public512Budget\n"
            "  match result.result with\n"
            "  | .error e => throw <| IO.userError (reprStr e)\n"
            "  | .ok c =>\n"
            f"      unless checkAt {args.native512_subject} c do\n"
            '        throw <| IO.userError "generated split certificate failed"\n'
            '      IO.println "NATIVE512_CHECKED"\n')
    command = ["lake", "build"]
    if args.native512_subject is not None:
        command.append("native512")
        command.append("Quickstart")
    result = subprocess.run(command, cwd=client, capture_output=True, text=True)
    native = None
    if result.returncode == 0 and args.native512_subject is not None:
        native = subprocess.run([str(client / ".lake/build/bin/native512")],
                                cwd=client, capture_output=True, text=True)
    sources = {str(p.relative_to(args.directory)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in args.directory.rglob("*") if p.is_file() and
               ".lake" not in p.relative_to(args.directory).parts and
               ".git" not in p.relative_to(args.directory).parts}
    forbidden = [str(p) for p in args.directory.rglob("*")
                 if p.is_dir() and p.name.lower() == "mathlib"]
    record = dict(source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                                 text=True).strip(),
                  command=command, cwd=str(client), returncode=result.returncode,
                  stdout=result.stdout, stderr=result.stderr, source_hashes=sources,
                  mathlib_directories=forbidden, skeleton_heads=skeleton_heads,
                  native512=None if native is None else dict(
                      subject=args.native512_subject, seed=args.seed,
                      returncode=native.returncode, stdout=native.stdout, stderr=native.stderr),
                  contract="Actual published repositories and sync transformations, coordinated next-release sources, local paths for exact staged "
                           "prerequisites. Full sync validators and version-pin/lockfile rewrites are covered by the guarded workflow dry run; this scratch build applies the source, generated Lake file and toolchain transforms and replaces requires with exact staged local paths. A fresh client uses the README verbatim. Lake "
                           "generates all lockfiles. No development project cache is reused.")
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode or forbidden or (native is not None and native.returncode):
        raise SystemExit(result.stdout + result.stderr + str(forbidden))
    print("Fresh ECPP split and README client passed without Mathlib")


if __name__ == "__main__":
    main()
