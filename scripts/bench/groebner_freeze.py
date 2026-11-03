#!/usr/bin/env python3
"""Build and freeze staged F4 driver sources and executable hashes for sweeps."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

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
    engine = source / "src/neogb/.libs/libneogb.so.4.0.0"
    commands = None
    if engine.is_file():
        recorded = subprocess.run(
            ["readelf", "-p", ".GCC.command.line", str(engine)],
            capture_output=True,
            text=True,
        )
        if recorded.returncode == 0 and "String dump" in recorded.stdout:
            commands = recorded.stdout
    if "-march=native" in (source / "src/neogb/Makefile").read_text():
        if commands is None or "-march=native" not in commands.split():
            raise ValueError("requested native CPU tuning is absent from recorded engine commands")
    return {
        "commit": git("rev-parse", "HEAD").decode().strip(),
        "tracked_status": status,
        "engine_recorded_compile_commands": commands,
        "tracked_diff_sha256": hashlib.sha256(diff).hexdigest(),
        "flags": {
            str(f.relative_to(source)): "\n".join(
                line for line in f.read_text().splitlines() if line.startswith(prefixes)
            )
            for f in [source / "Makefile", source / "src/neogb/Makefile"]
        },
        "generated_input_sha256": {
            str(f.relative_to(source)): sha(f)
            for f in [
                source / "Makefile",
                source / "src/neogb/Makefile",
                source / "config.h",
                source / "libtool",
            ]
            if f.is_file()
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


def compiler_provenance(native_cc: str | None = None) -> dict:
    prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    commands = {"native": native_cc or shutil.which("cc"), "other_native": shutil.which("cc"),
                "lean": os.environ.get("LEAN_CC", str(Path(prefix)/"bin/clang"))}
    result = {}
    for kind, command in commands.items():
        if command is None:
            raise ValueError("native C compiler is unavailable")
        path = Path(shutil.which(command) or command).resolve()
        result[kind] = {"command": command, "resolved": str(path), "sha256": sha(path),
                        "version": subprocess.check_output([command,"--version"], text=True)}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--sampled", action="store_true", help="also freeze both sampled driver initializers")
    parser.add_argument("--bench", action="store_true", help="also freeze the registered kernel benchmark executable")
    parser.add_argument("--avx512", action="store_true", help="enable experimental sixteen-lane native dispatch")
    parser.add_argument("--native-cc", help="override the Groebner C compiler through Lake configuration")
    parser.add_argument("--compiler-input", type=Path, action="append", default=[],
                        help="retain an external compiler wrapper/config input")
    args = parser.parse_args()
    if args.native_cc is not None:
        args.native_cc = str(Path(shutil.which(args.native_cc) or args.native_cc).absolute())
    listing = sources()
    compilers = compiler_provenance(args.native_cc)
    compiler_inputs = {str(path.resolve()):sha(path) for path in args.compiler_input}
    output = args.output.resolve()
    output.mkdir(exist_ok=False)
    executables = [("compute", "hexgroebner_compute"), ("compute-reference", "hexgroebner_compute_full")]
    if args.sampled:
        executables += [("sample", "hexgroebner_sample"), ("sample-reference", "hexgroebner_sample_full")]
    if args.bench:
        executables += [("bench", "hexgroebner_bench")]
    options = (["-KhexGroebnerAVX512=true"] if args.avx512 else [])
    options += (["-KhexGroebnerCC="+args.native_cc] if args.native_cc else [])
    command = ["lake", *(["-R", *options] if options else []),
               "build", *[target for _, target in executables]]
    tree = subprocess.check_output(["git", "write-tree"], cwd=ROOT, text=True).strip()
    parent = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()
    snapshot = subprocess.check_output(
        [
            "git",
            "commit-tree",
            tree,
            "-p",
            parent,
            "-m",
            "Freeze staged F4 driver sources",
        ],
        cwd=ROOT,
        text=True,
    ).strip()
    binaries = output / "binaries"
    binaries.mkdir()
    with tempfile.TemporaryDirectory(prefix="groebner-freeze-") as directory:
        checkout = Path(directory) / "source"
        subprocess.run(
            ["git", "worktree", "add", "--detach", str(checkout), snapshot],
            cwd=ROOT,
            check=True,
            capture_output=True,
        )
        try:
            (checkout / ".lake").mkdir(exist_ok=True)
            (checkout / ".lake/packages").symlink_to(
                (ROOT / ".lake/packages").resolve(), target_is_directory=True
            )
            with (output / "build.log").open("w") as log:
                subprocess.run(
                    command,
                    cwd=checkout,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    check=True,
                )
            for name, target in executables:
                original = checkout / ".lake/build/bin" / target
                shutil.copy2(original, binaries / name)
                if sha(original) != sha(binaries / name):
                    raise RuntimeError("executable changed while freezing")
        finally:
            subprocess.run(
                ["git", "worktree", "remove", "--force", str(checkout)],
                cwd=ROOT,
                check=True,
            )
    if sources() != listing:
        raise RuntimeError("sources changed during build")
    if compiler_provenance(args.native_cc) != compilers or any(sha(Path(path)) != digest for path,digest in compiler_inputs.items()):
        raise RuntimeError("compiler inputs changed during build")
    initialization = json.loads(
        subprocess.check_output(
            [
                sys.executable,
                "scripts/ci/check_groebner_initialization.py",
                "--default",
                str(binaries / "compute"),
                "--reference",
                str(binaries / "compute-reference"),
            ],
            cwd=ROOT,
            text=True,
        )
    )
    sampled_initialization = None
    if args.sampled:
        sampled_initialization = json.loads(subprocess.check_output([
            sys.executable,"scripts/ci/check_groebner_initialization.py",
            "--default",str(binaries / "sample"),"--reference",str(binaries / "sample-reference")],
            cwd=ROOT,text=True))
    manifest = {
        "source_fingerprint": fingerprint(listing),
        "native_options": {"hexGroebnerAVX512": args.avx512, "hexGroebnerCC": args.native_cc},
        "compilers": compilers,
        "compiler_inputs": compiler_inputs,
        "source_manifest": listing,
        "commit": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "binary_sha256": {f.name: sha(f) for f in binaries.iterdir()},
        "build_command": command,
        "build_policy": "fresh detached worktree of the staged index; only pinned dependency packages are shared",
        "source_tree": tree,
        "source_snapshot": snapshot,
        "initializer_checker_sha256": sha(
            ROOT / "scripts/ci/check_groebner_initialization.py"
        ),
        "build_log_sha256": sha(output / "build.log"),
        "freeze_script_sha256": sha(Path(__file__)),
        "initialization": initialization,
        "sampled_initialization": sampled_initialization,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    }
    for index,(path,digest) in enumerate(compiler_inputs.items()):
        destination = output / "compiler-inputs" / f"{index}-{Path(path).name}"
        destination.parent.mkdir(exist_ok=True)
        shutil.copy2(path,destination)
        if sha(destination) != digest:
            raise RuntimeError("compiler input copy differs")
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (output / "source.manifest").write_text(listing)
    for line in listing.splitlines():
        _, oid, rest = line.split(" ", 2)
        _, name = rest.split("\t")
        destination = output / "root-sources" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(
            subprocess.check_output(["git", "cat-file", "blob", oid], cwd=ROOT)
        )
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
