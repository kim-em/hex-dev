#!/usr/bin/env python3
"""Verify the standalone driver's selected initializer, without timing thresholds."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PINNED = "470d5ce1400764999581fd26d5d72b00d990b0f4"


def symbols(binary: Path) -> set[str]:
    output = subprocess.check_output(["nm", "-g", str(binary)], text=True)
    return {
        fields[-1].removeprefix("_")
        if fields[-1].startswith("_initialize_")
        else fields[-1]
        for line in output.splitlines()
        if len(fields := line.split()) >= 3 and fields[-2] != "U"
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--default", type=Path, default=ROOT / ".lake/build/bin/hexgroebner_compute"
    )
    parser.add_argument(
        "--reference",
        type=Path,
        default=ROOT / ".lake/build/bin/hexgroebner_compute_full",
    )
    args = parser.parse_args()
    revision = subprocess.check_output(
        ["lake", "env", "lean", "--githash"], cwd=ROOT, text=True
    ).strip()
    prefix = Path(
        subprocess.check_output(
            ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True
        ).strip()
    )
    archive = prefix / "lib/lean/libinitialize_minimal.a"
    minimal = revision == PINNED and archive.is_file()
    marker = "initialize_Lean_Elab_Frontend"
    reference, default = symbols(args.reference), symbols(args.default)
    assert marker in reference, "full-init reference lost the frontend initializer"
    assert (marker not in default) == minimal, (
        "default executable has the wrong initializer"
    )
    print(
        json.dumps(
            {
                "minimal_initialization": minimal,
                "compiler_revision": revision,
                "archive_sha256": hashlib.sha256(archive.read_bytes()).hexdigest()
                if minimal
                else None,
            }
        )
    )


if __name__ == "__main__":
    main()
