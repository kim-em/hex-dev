#!/usr/bin/env python3
"""Prepare and build the pinned SOS and CompPoly HexMvPoly consumers."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import sys


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


def configure_nix_sos_native_libs(destination: Path) -> None:
    """Teach the pinned SOS/CSDP lakefiles about Nix-store native libraries."""
    if not sys.platform.startswith("linux"):
        return
    standard_dirs = tuple(
        Path(path)
        for path in (
            "/usr/lib/x86_64-linux-gnu",
            "/usr/lib/aarch64-linux-gnu",
            "/usr/lib64",
            "/usr/lib",
        )
    )
    requirements = ("liblapack.so", "libblas.so", "libgfortran.so.5")
    if all(any((directory / name).exists() for directory in standard_dirs)
           for name in requirements):
        return

    store = Path("/nix/store")
    matches = {
        name: sorted(store.glob(f"*/lib/{name}")) if store.is_dir() else []
        for name in requirements
    }
    if not all(matches.values()):
        # Leave the upstream dependency check intact so it reports the normal
        # apt/dnf instructions rather than hiding a genuinely missing library.
        return
    library_dirs = sorted({paths[0].parent for paths in matches.values()})
    current_library_path = os.environ.get("LD_LIBRARY_PATH")
    os.environ["LD_LIBRARY_PATH"] = os.pathsep.join(
        [*(path.as_posix() for path in library_dirs)]
        + ([current_library_path] if current_library_path else [])
    )
    link_entries = "".join(f'      "-L{path.as_posix()}",\n' for path in library_dirs)
    check_entries = "".join(f'  "{path.as_posix()}",\n' for path in library_dirs)

    replace_exact(
        destination / "lakefile.lean",
        '    #["-L/usr/lib/x86_64-linux-gnu",',
        f"    #[{link_entries}"
        '      "-L/usr/lib/x86_64-linux-gnu",',
    )
    csdp_lakefile = destination / ".lake" / "packages" / "CSDP" / "lakefile.lean"
    replace_exact(
        csdp_lakefile,
        '    #[ "-L/usr/lib/x86_64-linux-gnu",',
        f"    #[{link_entries}"
        '      "-L/usr/lib/x86_64-linux-gnu",',
    )
    replace_exact(
        csdp_lakefile,
        "def linuxLibDirs : Array FilePath := #[\n",
        "def linuxLibDirs : Array FilePath := #[\n" + check_entries,
    )
    print(
        "configured SOS/CSDP Nix native library directories: "
        + ", ".join(path.as_posix() for path in library_dirs)
    )


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
    # CompPoly's pinned `ofPoly_zero` proof unfolds support internals that
    # changed between its v4.32.0 toolchain and Hex's v4.32.0-rc1 toolchain.
    # Reprove the same statement through CompPoly's public ring equivalence.
    replace_exact(
        destination / "CompPoly" / "Bivariate" / "ToPoly.lean",
        "lemma ofPoly_zero {R : Type*} [BEq R] [LawfulBEq R] "
        "[Nontrivial R] [Semiring R] [DecidableEq R] :\n"
        "    ofPoly (0 : R[X][Y]) = 0 := by\n"
        "      unfold CBivariate.ofPoly\n"
        "      simp +decide [ Polynomial.support ]",
        "lemma ofPoly_zero {R : Type*} [BEq R] [LawfulBEq R] "
        "[Nontrivial R] [Semiring R] [DecidableEq R] :\n"
        "    ofPoly (0 : R[X][Y]) = 0 := by\n"
        "  apply (ringEquiv (R := R)).injective\n"
        "  change toPoly (ofPoly (0 : R[X][Y])) = "
        "toPoly (0 : CBivariate R)\n"
        "  rw [ofPoly_toPoly, toPoly_zero]",
    )
    shutil.copyfile(
        ADAPTERS / "CompPolyBivariateCMvEquiv.lean",
        destination / "CompPoly" / "Bivariate" / "CMvEquiv.lean",
    )
    shutil.copyfile(
        ADAPTERS / "CompPolyUnivariateCMvEquiv.lean",
        destination / "CompPoly" / "Univariate" / "CMvEquiv.lean",
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
        configure_nix_sos_native_libs(sos)
    if not args.skip_build:
        if args.skip_update:
            raise RuntimeError("--skip-build is required together with --skip-update")
        run(
            [
                "lake",
                "build",
                "+SOS.Certificate:olean",
                "+SOS.EqElim:olean",
                "+SOS.Symmetry:olean",
                "+SOS.Verifier:olean",
                "+SOS.Tactic:olean",
                "+SOSTest.Examples:olean",
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
