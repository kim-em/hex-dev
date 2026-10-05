#!/usr/bin/env python3
"""Build a fresh downstream project against the repositories a sync would publish.

`sync_released.py --dry-run --stage STAGE` leaves every rewritten mirror in
`STAGE/<name>`. Unpublished dependencies use sibling directories; previously
published dependencies keep their immutable Git pins. A partial phase checks
only the selected libraries and their closure. A final phase creates
`STAGE/consumer`, an ordinary Lake project requiring the `hex` aggregate, and builds

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

try:
    from .sync_released import _import_roots
except ImportError:  # Direct script invocation.
    from sync_released import _import_roots

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


def point_at_stage(stage: Path, repo: Path, local_names: set[str] | None = None) -> None:
    """Require staged Hex repositories by relative path instead of by tag."""
    toml = repo / "lakefile.toml"
    if toml.is_file():
        blocks = re.split(r"(?m)^(?=\[)", toml.read_text(encoding="utf-8"))
        for i, block in enumerate(blocks):
            git = re.search(r'(?m)^git\s*=\s*"([^"]+)"\s*$', block)
            name = git and local_repo(git.group(1), stage)
            if block.startswith("[[require]]") and name and (local_names is None or name in local_names):
                block = re.sub(r'(?m)^rev\s*=.*\n?', "", block)
                blocks[i] = block.replace(git.group(0), f'path = "../{name}"')
        toml.write_text("".join(blocks), encoding="utf-8")
    lean = repo / "lakefile.lean"
    if lean.is_file():
        text = LEAN_REQUIRE.sub(
            lambda m: f'{m.group(1)}"../{m.group(2)}"'
            if (stage / m.group(2)).is_dir() and
            (local_names is None or m.group(2) in local_names) else m.group(0),
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
            if not ((name := local_repo(package.get("url") or "", stage)) and
                    (local_names is None or name in local_names))
        ]
        manifest.write_text(json.dumps(data, indent=1) + "\n", encoding="utf-8")


def imported_roots(path: Path) -> set[str]:
    return _import_roots(path.read_text(encoding="utf-8"))


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


def write_partial_consumer(stage: Path, entries: list[dict], selected: set[str],
                           local_names: set[str], version: str,
                           preferred_urls: dict[str, str] | None = None
                           ) -> tuple[Path, list[str]]:
    """Build the selected roots against their staged, possibly published, closure."""
    available = [e for e in entries if (stage / e["repo"].split("/")[-1]).is_dir()]
    roots = [e for e in available if e["repo"].split("/")[-1] in selected]
    consumer = stage / "consumer"
    source = consumer / "Consumer"
    source.mkdir(parents=True)
    shutil.copy(stage / roots[0]["repo"].split("/")[-1] / "lean-toolchain",
                consumer / "lean-toolchain")
    requires = ""
    for entry in roots:
        name = entry["repo"].split("/")[-1]
        url = (preferred_urls or {}).get(entry.get("lean_lib_name", entry["lib"]),
                                        f'https://github.com/{entry["repo"]}.git')
        location = (f'path = "../{name}"' if name in local_names else
                    f'git = "{url}"\nrev = "{version}"')
        requires += (f'[[require]]\nname = "{entry.get("lean_lib_name", entry["lib"])}"\n'
                     f'{location}\n\n')
    (consumer / "lakefile.toml").write_text(
        'name = "consumer"\n\n' + requires +
        '[[lean_lib]]\nname = "Consumer"\n\n'
        '[[lean_exe]]\nname = "consumer_link"\nroot = "Consumer.Main"\n')
    imports = [e.get("lean_lib_name", e["lib"]) for e in roots]
    (source / "Imports.lean").write_text("".join(f"import {lib}\n" for lib in imports))
    libraries = {e["lib"] for e in available}
    if "HexArith" in libraries:
        # Exercise the existing native link check even if Arith is an earlier dependency.
        (source / "Main.lean").write_text("import HexArith\n" + MAIN)
    else:
        (source / "Main.lean").write_text(
            'import Consumer.Imports\n\ndef main : IO Unit :=\n'
            '  IO.println "consumer link check passed"\n')
    modules = ["Consumer.Imports"]
    for entry in roots:
        modules.extend("+" + module for module in
                       (entry.get("test_modules") or []) + (entry.get("build_modules") or []))
    for example in sorted((REPO_ROOT / "Examples").glob("*.lean")):
        if imported_roots(example) <= libraries:
            target = source / "Examples" / example.name
            target.parent.mkdir(exist_ok=True)
            shutil.copy(example, target)
            modules.append(f"Consumer.Examples.{example.stem}")
    return consumer, modules


def run(cmd: list[str], cwd: Path) -> None:
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def pin_consumer_externals(consumer: Path, stage: Path, entries: list[dict],
                           plan: dict | None) -> None:
    """Test earlier mirrors against this phase's actual external dependencies."""
    if plan is None:
        return
    names = set()
    for entry in entries:
        lock = stage / entry["repo"].split("/")[-1] / "lake-manifest.json"
        if lock.is_file():
            names.update(p["name"] for p in json.loads(lock.read_text())["packages"])
    lakefile = consumer / "lakefile.toml"
    with lakefile.open("a") as output:
        for pin in plan["external_pins"].values():
            if pin["name"] in names:
                output.write(f'\n[[require]]\nname = "{pin["name"]}"\n'
                             f'git = "{pin["url"]}"\nrev = "{pin["rev"]}"\n')


def check_consumer_pins(consumer: Path, plan: dict | None) -> None:
    """Reject pin drift before cache retrieval or any Mathlib compilation."""
    document = json.loads((consumer / "lake-manifest.json").read_text())
    packages = {p["name"]: p for p in document["packages"]}

    def check(expected: dict) -> None:
        actual = packages.get(expected["name"])
        if (actual is None or actual.get("type") != "git" or
                actual.get("rev") != expected["rev"] or
                actual.get("url") != expected["url"] or
                actual.get("subDir") != expected.get("subDir")):
            raise RuntimeError(f'consumer resolved {expected["name"]} differently from '
                               "the checked publication or Mathlib lockfile")

    if plan:
        for expected in plan["external_pins"].values():
            if expected["name"] in packages:
                check(expected)
        completed = plan["baseline"].get("_pending_release", {}).get("repos", [])
        for package in packages.values():
            match = HEX_URL.match(package.get("url", ""))
            if match and match[1] in completed:
                if package.get("type") != "git" or package.get("rev") != plan["baseline"][match[1]]:
                    raise RuntimeError(f"consumer must retain the published pin of {match[1]}")
    if "mathlib" in packages:
        path = consumer / document.get("packagesDir", ".lake/packages") / "mathlib/lake-manifest.json"
        dependencies = json.loads(path.read_text())["packages"]
        for expected in dependencies:
            check(expected)


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
    plan_file = stage / "release-stage.json"
    plan = json.loads(plan_file.read_text()) if plan_file.exists() else None
    selected = set(plan["selected"]) if plan else {
        e["repo"].split("/")[-1] for e in entries}
    local_names = set(plan["fingerprints"]) if plan else selected
    known = {e["repo"].split("/")[-1] for e in entries}
    if not selected or selected - known:
        ap.error("release-stage.json contains an empty or unknown selection")
    aggregate_selected = any(e.get("pins_only") and
                             e["repo"].split("/")[-1] in selected for e in entries)
    available = [e for e in entries if (stage / e["repo"].split("/")[-1]).is_dir()]
    required = set(known if aggregate_selected else selected)
    for entry in entries:
        if entry["repo"].split("/")[-1] in selected:
            required.update(entry.get("pins") or [])
    for name in required:
        if not (stage / name).is_dir():
            ap.error(f"{stage / name} is missing from the selected dependency closure")
    for entry in available:
        repo = stage / entry["repo"].split("/")[-1]
        # Published dependencies keep Git sources matching Mathlib's manifest.
        # Only repositories this run would publish need unpublished path sources.
        point_at_stage(stage, repo, local_names)
    if not aggregate_selected:
        consumer, modules = write_partial_consumer(stage, entries, selected,
                                                   local_names, plan["version"] if plan else "",
                                                   {p["name"]: p["url"] for p in
                                                    plan.get("mathlib_dependencies", [])} if plan else {})
        pin_consumer_externals(consumer, stage, available, plan)
        run(["lake", "update"], consumer)
        check_consumer_pins(consumer, plan)
        lock = json.loads((consumer / "lake-manifest.json").read_text())
        if any(p.get("name") == "mathlib" for p in lock["packages"]):
            run(["lake", "exe", "cache", "get"], consumer)
        run(["lake", "build", *modules, "consumer_link"], consumer)
        run(["lake", "exe", "consumer_link"], consumer)
        return 0
    helper = write_helper_consumer(stage, entries)
    if helper is not None:
        project, targets = helper
        pin_consumer_externals(project, stage, [e for e in available
                               if not e.get("aggregate", True)], plan)
        run(["lake", "update"], project)
        check_consumer_pins(project, plan)
        run(["lake", "build", *targets], project)
    modules = write_consumer(stage, entries)
    consumer = stage / "consumer"
    pin_consumer_externals(consumer, stage, available, plan)
    run(["lake", "update"], consumer)
    check_consumer_pins(consumer, plan)
    run(["lake", "exe", "cache", "get"], consumer)
    run(["lake", "build", *modules, "consumer_link"], consumer)
    run(["lake", "exe", "consumer_link"], consumer)
    return 0


if __name__ == "__main__":
    sys.exit(main())
