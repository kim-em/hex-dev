#!/usr/bin/env python3
"""Prepare and build the pinned SOS and CompPoly HexMvPoly consumers."""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[2]
ADAPTERS = ROOT / "scripts" / "bench" / "hex_mv_poly_consumers"
SOS_URL = "https://github.com/leanprover/sos.git"
SOS_REV = "4e52845513a5a7f70927c96e094592db1bf124d1"
COMPPOLY_URL = "https://github.com/Verified-zkEVM/CompPoly.git"
COMPPOLY_REV = "f4c59f9e6a00b4e73f3e43ca362480468a508011"


def run(command: list[str], cwd: Path | None = None) -> None:
    subprocess.run(command, cwd=cwd, check=True)


def replace_exact(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(old) != 1:
        raise RuntimeError(f"{path} does not contain exactly one expected block")
    path.write_text(text.replace(old, new), encoding="utf-8")


def clone(url: str, revision: str, destination: Path) -> None:
    run(["git", "clone", url, str(destination)])
    run(["git", "checkout", "--detach", revision], destination)


def prepare_sos(destination: Path, hex_root: Path, toolchain: str) -> None:
    clone(SOS_URL, SOS_REV, destination)
    replace_exact(
        destination / "lakefile.lean",
        'require «CompPoly» from git\n'
        '  "https://github.com/Verified-zkEVM/CompPoly" @ "master"',
        f'require Hex from "{hex_root.as_posix()}"',
    )
    (destination / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    shutil.copyfile(
        ADAPTERS / "SOSHexMvPolyCompat.lean",
        destination / "SOS" / "HexMvPolyCompat.lean",
    )
    replace_exact(
        destination / "SOS" / "Certificate.lean",
        "import CompPoly.Multivariate.CMvPolynomial\n"
        "import CompPoly.Multivariate.Operations\n"
        "import CompPoly.Multivariate.MvPolyEquiv.Instances",
        "import SOS.HexMvPolyCompat",
    )
    replace_exact(
        destination / "SOS" / "EqElim.lean",
        "import CompPoly.Multivariate.Operations",
        "import SOS.HexMvPolyCompat",
    )
    replace_exact(
        destination / "SOS" / "Symmetry.lean",
        "import CompPoly.Multivariate.CMvPolynomial\n"
        "import CompPoly.Multivariate.Operations",
        "import SOS.HexMvPolyCompat",
    )
    verifier = destination / "SOS" / "Verifier.lean"
    text = verifier.read_text(encoding="utf-8")
    start_marker = "/-! ### CompPoly aeval helpers"
    end_marker = "/-! ### Reflection:"
    start = text.find(start_marker)
    end = text.find(end_marker)
    if start < 0 or end < 0 or start >= end:
        raise RuntimeError("pinned SOS verifier does not match expected input")
    verifier.write_text(text[:start] + text[end:], encoding="utf-8")


def prepare_comp_poly(
    destination: Path, hex_root: Path, toolchain: str
) -> None:
    clone(COMPPOLY_URL, COMPPOLY_REV, destination)
    replace_exact(
        destination / "lakefile.lean",
        'require "leanprover-community" / mathlib @ git "v4.32.0"',
        f'require Hex from "{hex_root.as_posix()}"',
    )
    (destination / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    shutil.copyfile(
        ADAPTERS / "CompPolyBivariateCMvEquiv.lean",
        destination / "CompPoly" / "Bivariate" / "CMvEquiv.lean",
    )
    shutil.copyfile(
        ADAPTERS / "CompPolyUnivariateCMvEquiv.lean",
        destination / "CompPoly" / "Univariate" / "CMvEquiv.lean",
    )
    replace_exact(
        destination / "CompPoly" / "Bivariate" / "ToPoly.lean",
        "    ofPoly (0 : R[X][Y]) = 0 := by\n"
        "      unfold CBivariate.ofPoly\n"
        "      simp +decide [ Polynomial.support ]",
        "    ofPoly (0 : R[X][Y]) = 0 := by\n"
        "  simpa [ringEquiv] using\n"
        "    (map_zero (ringEquiv (R := R)).symm)",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "destination",
        type=Path,
        help="new parent directory for the pinned consumer clones",
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
        help="prepare the clones without running `lake update`",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="prepare and update the clones without building acceptance targets",
    )
    args = parser.parse_args()

    destination = args.destination.resolve()
    hex_root = args.hex_root.resolve()
    if destination.exists():
        raise RuntimeError(f"destination already exists: {destination}")
    if not (hex_root / "lakefile.lean").is_file():
        raise RuntimeError(f"not a Hex source tree: {hex_root}")
    destination.mkdir(parents=True)

    toolchain = (hex_root / "lean-toolchain").read_text(encoding="utf-8")
    sos = destination / "sos"
    comp_poly = destination / "CompPoly"
    prepare_sos(sos, hex_root, toolchain)
    prepare_comp_poly(comp_poly, hex_root, toolchain)

    if not args.skip_update:
        run(["lake", "update"], sos)
        run(["lake", "update"], comp_poly)
    if not args.skip_build:
        if args.skip_update:
            raise RuntimeError("--skip-build is required together with --skip-update")
        run(
            [
                "lake",
                "build",
                "SOS.Certificate",
                "SOS.EqElim",
                "SOS.Symmetry",
                "+SOS.Verifier:olean",
            ],
            sos,
        )
        run(
            [
                "lake",
                "build",
                "CompPoly.Univariate.CMvEquiv",
                "CompPoly.Bivariate.CMvEquiv",
            ],
            comp_poly,
        )

    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
