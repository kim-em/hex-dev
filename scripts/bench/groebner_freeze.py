#!/usr/bin/env python3
"""Build and freeze staged F4 driver sources and executable hashes for sweeps."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.groebner_measure import FAMILY
from scripts.bench.sweep_freshness import fingerprint, index_listing


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def msolve_build(source: Path, require_clean: bool = True) -> dict:
    def git(*args):
        return subprocess.check_output(["git", *args], cwd=source)

    status = git("status", "--porcelain", "--untracked-files=no").decode()
    diff = git("diff", "HEAD", "--binary")
    if require_clean and (status or diff):
        raise ValueError("msolve source has tracked modifications")
    prefixes = (
        "CC =",
        "CFLAGS =",
        "CPPFLAGS =",
        "LDFLAGS =",
        "LIBS =",
        "SIMD_FLAGS =",
        "CPUEXT_FLAGS =",
        "OPENMP_CFLAGS =",
    )
    return {
        "commit": git("rev-parse", "HEAD").decode().strip(),
        "tracked_status": status,
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
        "flags": {
            str(f.relative_to(source)): "\n".join(
                line for line in f.read_text().splitlines() if line.startswith(prefixes)
            )
            for f in [source / "Makefile", source / "src/neogb/Makefile"]
        },
        "configure": subprocess.check_output(
            ["./config.status", "--config"], cwd=source, text=True
        ).strip(),
    }


def sources() -> str:
    dirty = subprocess.check_output(
        ["git", "diff", "--name-only"], cwd=ROOT, text=True
    ).splitlines()
    dirty += subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard"], cwd=ROOT, text=True
    ).splitlines()
    if any(FAMILY.matches(path) for path in dirty):
        raise ValueError("stage every measured source before freezing")
    return index_listing(FAMILY)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    listing = sources()
    output = args.output.resolve()
    output.mkdir(exist_ok=False)
    command = ["lake", "build", "hexgroebner_compute", "hexgroebner_compute_full"]
    with (output / "build.log").open("w") as log:
        subprocess.run(
            command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True
        )
    if sources() != listing:
        raise RuntimeError("sources changed during build")
    binaries = output / "binaries"
    binaries.mkdir()
    for name, target in [
        ("compute", "hexgroebner_compute"),
        ("compute-reference", "hexgroebner_compute_full"),
    ]:
        original = ROOT / ".lake/build/bin" / target
        shutil.copy2(original, binaries / name)
        if sha(original) != sha(binaries / name):
            raise RuntimeError("executable changed while freezing")
    initialization = json.loads(
        subprocess.check_output(
            [sys.executable, "scripts/ci/check_groebner_initialization.py"],
            cwd=ROOT,
            text=True,
        )
    )
    manifest = {
        "source_fingerprint": fingerprint(listing),
        "source_manifest": listing,
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "binary_sha256": {f.name: sha(f) for f in binaries.iterdir()},
        "build_command": command,
        "build_log_sha256": sha(output / "build.log"),
        "freeze_script_sha256": sha(Path(__file__)),
        "initialization": initialization,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (output / "source.manifest").write_text(listing)
    shutil.copy2(__file__, output / Path(__file__).name)
    print(
        json.dumps(
            {
                "source_fingerprint": manifest["source_fingerprint"],
                "binary_sha256": manifest["binary_sha256"],
            }
        )
    )


if __name__ == "__main__":
    main()
