#!/usr/bin/env python3
"""Prepare and build the pinned SOS and CompPoly HexMvPoly consumers."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
ADAPTERS = ROOT / "scripts" / "bench" / "hex_mv_poly_consumers"
SOS_URL = "https://github.com/leanprover/sos.git"
SOS_REV = "4e52845513a5a7f70927c96e094592db1bf124d1"
COMPPOLY_URL = "https://github.com/Verified-zkEVM/CompPoly.git"
COMPPOLY_REV = "f4c59f9e6a00b4e73f3e43ca362480468a508011"
SOS_TARGETS = [
    "+SOS.Certificate:olean",
    "+SOS.EqElim:olean",
    "+SOS.Symmetry:olean",
    "+SOS.Verifier:olean",
    "+SOS.Tactic:olean",
    "+SOSTest.Examples:olean",
]
COMPPOLY_TARGETS = [
    "CompPoly.Univariate.CMvEquiv",
    "CompPoly.Bivariate.CMvEquiv",
]


def run(command: list[str], cwd: Path | None = None) -> None:
    subprocess.run(command, cwd=cwd, check=True)


def run_output(command: list[str], cwd: Path) -> str:
    return subprocess.run(
        command,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()


def run_build(command: list[str], cwd: Path) -> dict[str, object]:
    process = subprocess.Popen(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert process.stdout is not None
    lines: list[str] = []
    for line in process.stdout:
        print(line, end="", flush=True)
        lines.append(line)
    return_code = process.wait()
    output = "".join(lines)
    if return_code != 0:
        raise subprocess.CalledProcessError(
            return_code, command, output=output
        )
    match = re.search(
        r"Build completed successfully \((\d+) jobs\)\.", output
    )
    if match is None:
        raise RuntimeError("could not find Lake's successful-build summary")
    return {
        "status": "passed",
        "jobs": int(match.group(1)),
        "output_sha256": hashlib.sha256(output.encode()).hexdigest(),
    }


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_source_state(source: Path) -> dict[str, object]:
    status = run_output(["git", "status", "--porcelain"], source)
    return {
        "commit": run_output(["git", "rev-parse", "HEAD"], source),
        "tree": run_output(["git", "rev-parse", "HEAD^{tree}"], source),
        "dirty": bool(status),
        "status": status.splitlines(),
    }


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
    parser.add_argument(
        "--output",
        type=Path,
        help="write machine-readable acceptance evidence after successful builds",
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
    source_state = git_source_state(hex_root)

    if not args.skip_update:
        run(["lake", "update"], sos)
        run(["lake", "update"], comp_poly)
        configure_nix_sos_native_libs(sos)
    build_results: dict[str, dict[str, object]] = {}
    if not args.skip_build:
        if args.skip_update:
            raise RuntimeError("--skip-build is required together with --skip-update")
        build_results["sos"] = run_build(
            ["lake", "build", *SOS_TARGETS], sos
        )
        build_results["comp_poly"] = run_build(
            ["lake", "build", *COMPPOLY_TARGETS], comp_poly
        )

    if args.output is not None:
        if args.skip_update or args.skip_build:
            raise RuntimeError("--output requires both update and build")
        evidence = {
            "schema": "hex-mv-poly-consumer-acceptance-v1",
            "generated_at_utc": datetime.now(timezone.utc).isoformat().replace(
                "+00:00", "Z"
            ),
            "toolchain": toolchain.strip(),
            "hex_source": source_state,
            "consumers": [
                {
                    "name": "SOS",
                    "url": SOS_URL,
                    "revision": SOS_REV,
                    "lake_manifest_sha256": sha256_file(
                        sos / "lake-manifest.json"
                    ),
                    "adapter_sha256": sha256_file(
                        sos / "SOS" / "HexMvPolyCompat.lean"
                    ),
                    "targets": SOS_TARGETS,
                    "build": build_results["sos"],
                },
                {
                    "name": "CompPoly",
                    "url": COMPPOLY_URL,
                    "revision": COMPPOLY_REV,
                    "lake_manifest_sha256": sha256_file(
                        comp_poly / "lake-manifest.json"
                    ),
                    "adapter_sha256": {
                        "univariate": sha256_file(
                            comp_poly
                            / "CompPoly"
                            / "Univariate"
                            / "CMvEquiv.lean"
                        ),
                        "bivariate": sha256_file(
                            comp_poly
                            / "CompPoly"
                            / "Bivariate"
                            / "CMvEquiv.lean"
                        ),
                    },
                    "targets": COMPPOLY_TARGETS,
                    "build": build_results["comp_poly"],
                },
            ],
            "acceptance_passed": True,
        }
        output = args.output.resolve()
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(
            json.dumps(evidence, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(output)
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
