#!/usr/bin/env python3
"""Check exact frozen suggestions and fresh computational replay; --gp adds live GP."""
from __future__ import annotations
import argparse
from contextlib import contextmanager
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def build(module: str, env: dict[str, str], error: str | None = None) -> str:
    result = subprocess.run(["lake", "build", f"+{module}:olean"], cwd=ROOT,
                            env=env, text=True, capture_output=True, timeout=180)
    output = result.stdout + result.stderr
    if error is None and result.returncode:
        raise RuntimeError(output)
    if error is not None and (not result.returncode or error not in output):
        raise RuntimeError(f"expected {error!r}:\n{output}")
    return output


@contextmanager
def scratch_modules():
    with tempfile.TemporaryDirectory(prefix="ExternalScratch", dir=ROOT / "HexIntFactor") as temp:
        path = Path(temp)
        try:
            yield path
        finally:
            for base in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
                shutil.rmtree(base / "HexIntFactor" / path.name, ignore_errors=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", help="also test a real GP executable")
    args = parser.parse_args()
    env = dict(os.environ, HEX_INT_FACTOR_GP="/hex-no-factorizer-on-replay")
    with scratch_modules() as scratch:
        module = "HexIntFactor." + scratch.name
        # Extract the exact complete and partial suggestions pinned by #guard_msgs.
        tests = (ROOT / "HexIntFactor/ExportTests.lean").read_text()
        suggestions = re.findall(r"info: (module\n.*?⟨certificate, rfl, by decide \+kernel⟩)\n-/", tests, re.S)
        assert len(suggestions) == 2
        for name, text, checked in zip(("Complete", "Partial"), suggestions,
                                       ("CheckedFactorization", "CheckedPartialFactorization")):
            (scratch / f"{name}.lean").write_text(text + "\n")
            build(f"{module}.{name}", env)
            (scratch / f"Use{name}.lean").write_text(
                f"module\npublic import {module}.{name}\npublic section\n"
                f"example : Hex.Nat.{checked} 12 := certificate_checked\n"
                "#print axioms certificate_checked\n")
            output = build(f"{module}.Use{name}", env)
            assert "depends on axioms: [propext]" in output or "does not depend on any axioms" in output, output
        (scratch / "WrongSubject.lean").write_text(
            f"import {module}.Complete\n"
            "def wrong : Hex.Nat.CheckedFactorization 13 := certificate_checked\n")
        build(module + ".WrongSubject", env, "Type mismatch")
        (scratch / "Opaque.lean").write_text(
            "import HexIntFactor.Replay\n"
            "opaque hidden : Hex.Nat.Factorization := ⟨12, [⟨2, .small 2⟩, ⟨1, .small 3⟩]⟩\n"
            "example : Hex.Nat.checkFactorization hidden = true := by decide +kernel\n")
        build(module + ".Opaque", env, "failed")
        (scratch / "Editor.lean").write_text(
            "import HexIntFactor.Export\nset_option Elab.inServer true in\n"
            "#int_factor for 12\nset_option Elab.inServer true in\n"
            f"#int_factor_export {module}.EditorOutput cert for 12\n")
        build(module + ".Editor", env)
        assert not (scratch / "EditorOutput.lean").exists()
        # Refuse an existing destination before production, with no backend installed.
        destination = scratch / "Existing.lean"
        destination.write_text("preserve me\n")
        (scratch / "Again.lean").write_text(
            "import HexIntFactor.Export\n"
            f"#int_factor_export {module}.Existing cert for 12\n")
        build(module + ".Again", env, "already exists")
        assert destination.read_text() == "preserve me\n"
        (scratch / "BadNames.lean").write_text(
            'import HexIntFactor.Export\n#int_factor_export «../escape» cert for 12\n'
            f'#int_factor_export {module}.Unused invalid.name for 12\n')
        output = build(module + ".BadNames", env, "ASCII identifier components")
        assert "without a namespace" in output
        if args.gp:
            real_env = dict(env, HEX_INT_FACTOR_GP=str(Path(args.gp).resolve()))
            (scratch / "Real.lean").write_text(
                "import HexIntFactor.Export\n"
                f"#int_factor_export {module}.RealCertificate cert for 72\n"
                "#int_factor for 12\n")
            output = build(module + ".Real", real_env)
            match = re.search(r"Frozen certificate:\n(.*?⟨certificate, rfl, by decide \+kernel⟩)", output, re.S)
            assert match and match.group(1) == suggestions[0]
            build(module + ".RealCertificate", env)
        print("integer factor export: exact complete/partial text, exclusive creation, "
              "editor gating and fresh computational replay passed")


if __name__ == "__main__":
    main()
