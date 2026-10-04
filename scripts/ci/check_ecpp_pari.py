#!/usr/bin/env python3
"""Exercise PARI generation/export and rebuild the result with GP unavailable.

CI uses a protocol stub returning frozen PARI data. --gp runs the same test
with a real executable; neither route trusts the producer's output.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]


@contextmanager
def scratch_modules():
    with tempfile.TemporaryDirectory(prefix="PariScratch", dir=ROOT / "HexECPPMathlib") as scratch:
        path = Path(scratch)
        try:
            yield path
        finally:
            for folder in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
                shutil.rmtree(folder / "HexECPPMathlib" / path.name, ignore_errors=True)


def build(module: str, env: dict[str, str], *, expected_error: str | None = None, timeout: int = 120) -> str:
    result = subprocess.run(
        ["lake", "build", f"+{module}:olean"], cwd=ROOT, env=env,
        text=True, capture_output=True, timeout=timeout,
    )
    output = result.stdout + result.stderr
    if expected_error is None:
        if result.returncode:
            raise RuntimeError(output)
    elif result.returncode == 0 or expected_error not in output:
        raise RuntimeError(f"expected {expected_error!r}:\n{output}")
    return output


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", help="real GP executable; default uses a frozen protocol stub")
    parser.add_argument("--bits", type=int, choices=(65, 256, 512), default=65)
    args = parser.parse_args()
    fixture = ROOT / "conformance/HexECPP" / (
        "ImportConformance.lean" if args.bits == 65 else "PariFixtures.lean")
    source = fixture.read_text()
    payload = json.loads(re.search(
        rf'def pari{args.bits} : String :=\s*("[^\n]*")', source).group(1))
    n = json.loads(payload)[0][0]
    with scratch_modules() as scratch_path:
        module = "HexECPPMathlib." + scratch_path.name
        with tempfile.TemporaryDirectory(prefix="hex-gp-") as tools:
            tools_path = Path(tools)
            gp = tools_path / "gp"
            if args.gp:
                gp.symlink_to(Path(args.gp).resolve())
            else:
                gp.write_text(f"#!{sys.executable}\nimport sys\n"
                              "assert sys.argv[1:5] == ['-q', '-f', '-s', '64000000']\n"
                              "assert len(sys.argv) == 6\n"
                              "assert 'primecert(' in open(sys.argv[5]).read()\n"
                              f"print('HEX_ECPP_BEGIN\\n' + {payload!r} + '\\nHEX_ECPP_END')\n")
                gp.chmod(0o755)
            env = dict(os.environ, PATH=str(tools_path) + os.pathsep + os.environ["PATH"])
            (scratch_path / "Generate.lean").write_text(
                "module\n\nimport HexECPPMathlib.Pari\n\n"
                f"#ecpp_export {module}.Certificate cert for {n}\n\n"
                f"theorem result : Nat.Prime ({n} - 1 + 1) := by\n  primality? (method := pari)\n\n"
                "#print axioms result\n"
                f"example : Hex.Nat.Prime ({n} - 1 + 1) := by primality? (method := pari)\n")
            output = build(module + ".Generate", env)
            assert "Try this:" in output and "ecpp_cert%" in output
            assert "[propext, Classical.choice, Quot.sound]" in " ".join(output.split())
            suggestions = re.findall(
                r'Try this:\n  \[apply\] (.*?)(?=\n(?:info:|warning:|error:|✔|ℹ|Build|Some)|\Z)',
                output, re.S)
            suggestions = [s for s in suggestions if "ecpp_cert%" in s]
            assert len(suggestions) == 2, output
            certificate = scratch_path / "Certificate.lean"
            frozen = certificate.read_bytes()
            assert frozen.startswith(b"module\n"), frozen
            assert b"@[expose] public def" in b" ".join(frozen.split()), frozen
            assert b"ecpp_cert%" in frozen and b"method := pari" not in frozen
            assert len(frozen) < 17000
            # The export command refuses to overwrite a file, before calling GP.
            (scratch_path / "Again.lean").write_text(
                "module\n\nimport HexECPPMathlib.Pari\n"
                f"#ecpp_export {module}.Certificate cert for {n}\n")
            build(module + ".Again", env, expected_error="already exists")
            assert certificate.read_bytes() == frozen
            gp.unlink()
            accessed = tools_path / "accessed"
            gp.write_text(f"#!{sys.executable}\nfrom pathlib import Path\n"
                          f"Path({str(accessed)!r}).touch()\nraise SystemExit(99)\n")
            gp.chmod(0o755)
            (scratch_path / "Frozen.lean").write_text(
                f"module\n\npublic import {module}.Certificate\n\n"
                f"theorem result : Nat.Prime {n} := by\n"
                f"  ecpp using {module}.Certificate.cert\n\n#print axioms result\n"
                f"theorem suggestedNat : Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[0].strip() + "\n\n"
                f"theorem suggestedCore : Hex.Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[1].strip() + "\n")
            output = build(module + ".Frozen", env)
            assert "[propext, Classical.choice, Quot.sound]" in " ".join(output.split())
            assert not accessed.exists(), "frozen proof invoked GP"
            (scratch_path / "Editor.lean").write_text(
                "module\n\nimport HexECPPMathlib.Pari\nset_option Elab.inServer true in\n"
                f"#ecpp_export {module}.EditorOutput cert for 5\n")
            build(module + ".Editor", env)
            assert not accessed.exists(), "editor export invoked GP"
            assert not (scratch_path / "EditorOutput.lean").exists()
            (scratch_path / "InvalidNames.lean").write_text(
                'module\n\nimport HexECPPMathlib.Pari\n#ecpp_export «../escape» cert for 17\n'
                f'#ecpp_export {module}.Unused invalid.name for 17\n')
            output = build(module + ".InvalidNames", env, expected_error="ASCII identifier components")
            assert "without a namespace" in output
            assert not accessed.exists(), "invalid export invoked GP"
            print(json.dumps({"bits": args.bits, "producer": "real GP" if args.gp else "stub",
                              "frozen_source_bytes": len(frozen),
                              "sha256": hashlib.sha256(frozen).hexdigest(),
                              "kernel_replay_without_gp": True}))


if __name__ == "__main__":
    main()
