#!/usr/bin/env python3
"""Exercise PARI generation/export and rebuild the result with GP unavailable.

CI uses a protocol stub returning frozen PARI data. --gp runs the same test
with a real executable; neither route trusts the producer's output.
"""
from __future__ import annotations

import argparse
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


def build(module: str, env: dict[str, str], *, expected_error: str | None = None) -> str:
    result = subprocess.run(
        ["lake", "build", f"+{module}:olean"], cwd=ROOT, env=env,
        text=True, capture_output=True, timeout=120,
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
    with tempfile.TemporaryDirectory(prefix="PariScratch", dir=ROOT / "HexECPPMathlib") as scratch:
        scratch_path = Path(scratch)
        module = "HexECPPMathlib." + scratch_path.name
        with tempfile.TemporaryDirectory(prefix="hex-gp-") as tools:
            tools_path = Path(tools)
            gp = tools_path / "gp"
            if args.gp:
                gp.symlink_to(Path(args.gp).resolve())
            else:
                gp.write_text(f"#!{sys.executable}\nimport sys\n"
                              "assert sys.argv[1:] == ['-q', '-f', '-s', '64000000']\n"
                              "sys.stdin.read()\n"
                              f"print('HEX_ECPP_BEGIN\\n' + {payload!r} + '\\nHEX_ECPP_END')\n")
                gp.chmod(0o755)
            env = dict(os.environ, PATH=str(tools_path) + os.pathsep + os.environ["PATH"])
            (scratch_path / "Generate.lean").write_text(
                "import HexECPPMathlib.Pari\n\n"
                f"#ecpp_export {module}.Certificate cert for {n}\n\n"
                f"theorem result : Nat.Prime {n} := by\n  primality? (method := pari)\n\n"
                "#print axioms result\n"
                f"example : Hex.Nat.Prime {n} := by primality? (method := pari)\n")
            output = build(module + ".Generate", env)
            assert "Try this:" in output and "ecpp_cert%" in output
            assert "[propext, Classical.choice, Quot.sound]" in output
            suggestions = re.findall(
                r'Try this:\n  \[apply\] (.*?)(?=\n(?:info:|warning:|error:|✔|ℹ|Build|Some)|\Z)',
                output, re.S)
            suggestions = [s for s in suggestions if "ecpp_cert%" in s]
            assert len(suggestions) == 2, output
            certificate = scratch_path / "Certificate.lean"
            frozen = certificate.read_bytes()
            assert b"ecpp_cert%" in frozen and b"method := pari" not in frozen
            assert len(frozen) < 17000
            # The export command refuses to overwrite a file, before calling GP.
            (scratch_path / "Again.lean").write_text(
                "import HexECPPMathlib.Pari\n"
                f"#ecpp_export {module}.Certificate cert for {n}\n")
            build(module + ".Again", env, expected_error="already exists")
            assert certificate.read_bytes() == frozen
            gp.unlink()
            accessed = tools_path / "accessed"
            gp.write_text(f"#!{sys.executable}\nfrom pathlib import Path\n"
                          f"Path({str(accessed)!r}).touch()\nraise SystemExit(99)\n")
            gp.chmod(0o755)
            (scratch_path / "Frozen.lean").write_text(
                f"import {module}.Certificate\n\n"
                f"theorem result : Nat.Prime {n} := by\n"
                f"  ecpp using {module}.Certificate.cert\n\n#print axioms result\n"
                f"example : Nat.Prime {n} := by\n  " + suggestions[0].strip() + "\n\n"
                f"example : Hex.Nat.Prime {n} := by\n  " + suggestions[1].strip() + "\n")
            output = build(module + ".Frozen", env)
            assert "[propext, Classical.choice, Quot.sound]" in output
            assert not accessed.exists(), "frozen proof invoked GP"
            print(json.dumps({"bits": args.bits, "producer": "real GP" if args.gp else "stub",
                              "frozen_source_bytes": len(frozen),
                              "sha256": hashlib.sha256(frozen).hexdigest(),
                              "kernel_replay_without_gp": True}))
        # Scratch modules also leave generated Lake outputs; remove only ours.
        for folder in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
            shutil.rmtree(folder / "HexECPPMathlib" / scratch_path.name, ignore_errors=True)


if __name__ == "__main__":
    main()
