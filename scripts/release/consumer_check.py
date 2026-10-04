#!/usr/bin/env python3
"""Build a fresh downstream project against the repositories a sync would publish.

`sync_released.py --dry-run --stage STAGE` leaves every rewritten mirror in
`STAGE/<name>`, requiring its Hex dependencies at a release tag that does not
exist yet. This script points those requirements at the sibling directories,
then creates `STAGE/consumer`: an ordinary Lake project that requires the `hex`
aggregate exactly as a user would, and builds

- one module importing every published library umbrella,
- aggregate entries' `test_modules`, from the staged repositories,
- every `Examples/*.lean` user story whose imports are all published, and
- an executable that links the whole published closure and calls native code.

Elaborating in a downstream package is what exercises `precompileModules`, the
FFI targets and their link arguments the way a user meets them, on whichever
platform runs this script. Non-aggregate libraries are checked first in
`STAGE/helper-consumer`, with their tests and ordinary umbrella imports, so the
aggregate's default `Hex` root cannot capture test-kit modules. Run from the
repository root.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]
MANIFEST = REPO_ROOT / "scripts" / "release" / "released.yml"
HEX_URL = re.compile(r"https://github\.com/leanprover/([A-Za-z0-9_-]+?)(?:\.git)?$")
LEAN_REQUIRE = re.compile(
    r'(require\s+\S+\s+from\s+)git\s*\n?\s*"https://github\.com/leanprover/'
    r'([A-Za-z0-9_-]+?)(?:\.git)?"\s*@\s*"[^"]*"'
)
MAIN = """import Consumer.Imports

def main : IO Unit := do
  -- `extGcd` runs through HexArith's GMP-backed extern in compiled code.
  let (g, s, t) := HexArith.Int.extGcd 240 46
  unless g == 2 && s * 240 + t * 46 == 2 do
    throw <| IO.userError s!"extGcd 240 46 returned {(g, s, t)}"
  IO.println "consumer link check passed"
"""


def local_repo(url: str, stage: Path) -> str | None:
    match = HEX_URL.match(url)
    if match and (stage / match.group(1)).is_dir():
        return match.group(1)
    return None


def point_at_stage(stage: Path, repo: Path) -> None:
    """Require staged Hex repositories by relative path instead of by tag."""
    toml = repo / "lakefile.toml"
    if toml.is_file():
        blocks = re.split(r"(?m)^(?=\[)", toml.read_text(encoding="utf-8"))
        for i, block in enumerate(blocks):
            git = re.search(r'(?m)^git\s*=\s*"([^"]+)"\s*$', block)
            name = git and local_repo(git.group(1), stage)
            if block.startswith("[[require]]") and name:
                block = re.sub(r'(?m)^rev\s*=.*\n?', "", block)
                blocks[i] = block.replace(git.group(0), f'path = "../{name}"')
        toml.write_text("".join(blocks), encoding="utf-8")
    lean = repo / "lakefile.lean"
    if lean.is_file():
        text = LEAN_REQUIRE.sub(
            lambda m: f'{m.group(1)}"../{m.group(2)}"'
            if (stage / m.group(2)).is_dir() else m.group(0),
            lean.read_text(encoding="utf-8"),
        )
        lean.write_text(text, encoding="utf-8")
    manifest = repo / "lake-manifest.json"
    if manifest.is_file():
        # Dropping a Hex entry makes Lake resolve it from the lakefile's path
        # requirement; external pins (Mathlib, batteries) stay as recorded.
        data = json.loads(manifest.read_text(encoding="utf-8"))
        data["packages"] = [
            package for package in data["packages"]
            if not local_repo(package.get("url") or "", stage)
        ]
        manifest.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")


def imported_roots(path: Path) -> set[str]:
    return {
        match.group(1).split(".")[0]
        for match in re.finditer(
            r"(?m)^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)",
            path.read_text(encoding="utf-8"),
        )
    }


def write_consumer(stage: Path, entries: list[dict]) -> list[str]:
    """Create `STAGE/consumer` and return the modules it must build."""
    consumer = stage / "consumer"
    source = consumer / "Consumer"
    source.mkdir(parents=True)
    shutil.copy(stage / "hex" / "lean-toolchain", consumer / "lean-toolchain")
    libs = [e["lib"] for e in entries if not e.get("pins_only") and e.get("aggregate", True)]
    (consumer / "lakefile.toml").write_text(
        'name = "consumer"\n\n'
        '[[require]]\nname = "hex"\npath = "../hex"\n\n'
        '[[lean_lib]]\nname = "Consumer"\n\n'
        '[[lean_exe]]\nname = "consumer_link"\nroot = "Consumer.Main"\n',
        encoding="utf-8",
    )
    (source / "Imports.lean").write_text(
        "".join(f"import {lib}\n" for lib in libs), encoding="utf-8")
    (source / "Main.lean").write_text(MAIN, encoding="utf-8")
    modules = ["Consumer.Imports", "+Hex"]
    # Built in place: a copy would change the private names some
    # `#guard_msgs` outputs quote.
    for entry in entries:
        if not entry.get("pins_only") and entry.get("aggregate", True):
            modules.extend(f"+{test}" for test in entry.get("test_modules") or [])
    for example in sorted((REPO_ROOT / "Examples").glob("*.lean")):
        roots = imported_roots(example)
        # Only libraries the consumer reaches through `hex` are eligible.
        if roots <= set(libs):
            target = source / "Examples" / example.name
            target.parent.mkdir(exist_ok=True)
            shutil.copy(example, target)
            modules.append(f"Consumer.Examples.{example.stem}")
        else:
            print(f"skipping Examples/{example.name}: imports libraries outside the aggregate "
                  f"{sorted(roots - set(libs))}")
    return modules


def write_helper_consumer(stage: Path, entries: list[dict]) -> tuple[Path, list[str]] | None:
    """Check non-aggregate packages separately from the aggregate's Hex root.

    Lake's default Hex root claims absent Hex.* modules supplied by the test
    kit. Separate downstream projects preserve each published declaration and
    check both packages without relying on ambiguous module ownership.
    """
    others = [e for e in entries if not e.get("pins_only") and not e.get("aggregate", True)]
    if not others:
        return None
    consumer = stage / "helper-consumer"
    consumer.mkdir()
    shutil.copy(stage / "hex" / "lean-toolchain", consumer / "lean-toolchain")
    requires = "".join(
        f'[[require]]\nname = "{e.get("lean_lib_name", e["lib"])}"\n'
        f'path = "../{e["repo"].split("/")[-1]}"\n\n' for e in others)
    (consumer / "lakefile.toml").write_text(
        'name = "helper-consumer"\n\n' + requires +
        '[[lean_lib]]\nname = "HelperConsumer"\n', encoding="utf-8")
    (consumer / "HelperConsumer.lean").write_text(
        "".join(f'import {e.get("lean_lib_name", e["lib"])}\n' for e in others),
        encoding="utf-8")
    modules = ["HelperConsumer"]
    for entry in others:
        modules.append(entry.get("lean_lib_name", entry["lib"]))
        modules.extend("+" + test for test in entry.get("test_modules") or [])
    return consumer, modules


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", type=Path,
                    help="directory filled by sync_released.py --dry-run --stage")
    args = ap.parse_args()
    stage = args.stage.resolve()
    for name in ("consumer", "helper-consumer"):
        if (stage / name).exists():
            ap.error(f"{stage / name} already exists")
    entries = yaml.safe_load(MANIFEST.read_text(encoding="utf-8"))["repos"]
    for entry in entries:
        repo = stage / entry["repo"].split("/")[-1]
        if not repo.is_dir():
            ap.error(f"{repo} is missing; stage every repository (no --only)")
        point_at_stage(stage, repo)
    helper = write_helper_consumer(stage, entries)
    if helper is not None:
        project, targets = helper
        run(["lake", "update"], project)
        run(["lake", "build", *targets], project)
    modules = write_consumer(stage, entries)
    consumer = stage / "consumer"
    run(["lake", "update"], consumer)
    run(["lake", "exe", "cache", "get"], consumer)
    run(["lake", "build", *modules, "consumer_link"], consumer)
    run(["lake", "exe", "consumer_link"], consumer)
    return 0


if __name__ == "__main__":
    sys.exit(main())
