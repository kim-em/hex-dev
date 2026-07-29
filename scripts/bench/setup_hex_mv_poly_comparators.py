#!/usr/bin/env python3
"""Prepare the pinned external HexMvPoly native-comparator project."""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[2]
ADAPTERS = ROOT / "scripts" / "bench" / "hex_mv_poly_comparator"
COMPPOLY_URL = "https://github.com/Verified-zkEVM/CompPoly.git"
COMPPOLY_REV = "f4c59f9e6a00b4e73f3e43ca362480468a508011"
TOOLCHAIN = "leanprover/lean4:v4.32.0-rc1\n"
MATHLIB_REQUIRE = (
    'require "leanprover-community" / mathlib @ git "v4.32.0"'
)
EXE_DECLARATIONS = """

lean_exe comp_poly_mvpoly_bench where
  root := `CompPoly.MvPolyBench

lean_exe sorted_mvpoly_bench where
  root := `CompPoly.MvPolySortedBench
"""


def run(command: list[str], cwd: Path | None = None) -> None:
    subprocess.run(command, cwd=cwd, check=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "destination",
        type=Path,
        help="new directory in which to prepare the pinned CompPoly clone",
    )
    parser.add_argument(
        "--hex-root",
        type=Path,
        default=ROOT,
        help="Hex source tree used as the local Lake dependency",
    )
    parser.add_argument(
        "--skip-update",
        action="store_true",
        help="configure the clone without running `lake update`",
    )
    args = parser.parse_args()

    destination = args.destination.resolve()
    hex_root = args.hex_root.resolve()
    if destination.exists():
        raise RuntimeError(f"destination already exists: {destination}")
    if not (hex_root / "lakefile.lean").is_file():
        raise RuntimeError(f"not a Hex source tree: {hex_root}")

    run(["git", "clone", COMPPOLY_URL, str(destination)])
    run(["git", "checkout", "--detach", COMPPOLY_REV], destination)

    lakefile = destination / "lakefile.lean"
    lake_text = lakefile.read_text(encoding="utf-8")
    if lake_text.count(MATHLIB_REQUIRE) != 1:
        raise RuntimeError("pinned CompPoly lakefile does not match expected input")
    lake_text = lake_text.replace(
        MATHLIB_REQUIRE,
        f'require Hex from "{hex_root.as_posix()}"',
    )
    lakefile.write_text(lake_text + EXE_DECLARATIONS, encoding="utf-8")
    (destination / "lean-toolchain").write_text(TOOLCHAIN, encoding="utf-8")

    shutil.copyfile(
        ADAPTERS / "CompPolyMvPolyBench.lean",
        destination / "CompPoly" / "MvPolyBench.lean",
    )
    shutil.copyfile(
        ADAPTERS / "SortedMvPolyBench.lean",
        destination / "CompPoly" / "MvPolySortedBench.lean",
    )

    if not args.skip_update:
        run(["lake", "update"], destination)

    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
