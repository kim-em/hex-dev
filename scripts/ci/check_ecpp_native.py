#!/usr/bin/env python3
"""Generate native ECPP suggestions/export, then replay with search and GP absent."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

from check_ecpp_pari import build, scratch_modules


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--subject", type=int, default=177080666831933235355717939809840315427)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    n, seed = args.subject, args.seed
    with scratch_modules() as scratch:
        module = "HexECPPMathlib." + scratch.name
        with tempfile.TemporaryDirectory(prefix="hex-no-gp-") as folder:
            tools = Path(folder)
            marker = tools / "invoked"
            gp = tools / "gp"
            gp.write_text(f"#!{sys.executable}\nfrom pathlib import Path\n"
                          f"Path({str(marker)!r}).touch()\nraise SystemExit(99)\n")
            gp.chmod(0o755)
            env = dict(os.environ, PATH=str(tools) + os.pathsep + os.environ["PATH"])
            (scratch / "Generate.lean").write_text(
                "module\n\nimport HexECPPMathlib.Native\n\n"
                f"#ecpp_export (method := ecpp) (seed := {seed}) {module}.Certificate cert for {n}\n"
                f"theorem result : Nat.Prime ({n} - 1 + 1) := by\n"
                f"  primality? (method := ecpp) (seed := {seed})\n\n#print axioms result\n"
                f"example : Hex.Nat.Prime ({n} - 1 + 1) := by\n"
                f"  primality? (method := ecpp) (seed := {seed})\n")
            output = build(module + ".Generate", env)
            assert "[propext, Classical.choice, Quot.sound]" in " ".join(output.split()), output
            suggestions = re.findall(
                r'Try this:\n  \[apply\] (.*?)(?=\n(?:info:|warning:|error:|✔|ℹ|Build|Some)|\Z)',
                output, re.S)
            suggestions = [s for s in suggestions if "ecpp_cert%" in s]
            assert len(suggestions) == 2, output
            certificate = scratch / "Certificate.lean"
            frozen = certificate.read_bytes()
            assert frozen.startswith(b"module\n"), frozen
            assert b"@[expose] public def" in b" ".join(frozen.split()), frozen
            assert b"ecpp_cert%" in frozen and b"Native" not in frozen
            (scratch / "Frozen.lean").write_text(
                f"module\n\npublic import {module}.Certificate\n\n"
                f"theorem result : Nat.Prime {n} := by\n  ecpp using {module}.Certificate.cert\n"
                "\n#print axioms result\n"
                f"theorem suggestedNat : Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[0].strip() + "\n\n"
                f"theorem suggestedCore : Hex.Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[1].strip() + "\n")
            output = build(module + ".Frozen", env)
            assert "[propext, Classical.choice, Quot.sound]" in " ".join(output.split()), output
            # Private theorem names may repeat across independently built modules.
            # Importing the modules together must preserve their certificate data.
            (scratch / "Peer.lean").write_text(
                "module\n\npublic import HexECPPMathlib.Compact\n\n"
                "theorem suggestedNat : Nat.Prime (13 - 1 + 1) := by\n"
                '  ecpp using (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                "namespace First\nprivate theorem sameName : Nat.Prime 13 := by\n"
                '  ecpp using (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                "end First\nnamespace Second\nprivate theorem sameName : Nat.Prime 17 := by\n"
                '  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n'
                "end Second\n")
            (scratch / "PeerTwo.lean").write_text(
                "module\n\npublic import HexECPPMathlib.Compact\n\n"
                "theorem suggestedNat : Nat.Prime (17 - 1 + 1) := by\n"
                '  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n')
            # Prefix concatenation alone is ambiguous: these private theorem
            # prefixes plus module names coincide without a delimiter.
            (scratch / "Main.lean").write_text(
                "module\n\npublic import HexECPPMathlib.Compact\n\n"
                f"namespace p.sameName.{module}\n"
                "private theorem sameName : Nat.Prime 13 := by\n"
                '  ecpp using (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                f"end p.sameName.{module}\n")
            nested = scratch / "sameName" / Path(*module.split("."))
            nested.mkdir(parents=True)
            (nested / "Main.lean").write_text(
                "module\n\npublic import HexECPPMathlib.Compact\n\n"
                "namespace p\nprivate theorem sameName : Nat.Prime 17 := by\n"
                '  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n'
                "end p\n")
            (scratch / "Combined.lean").write_text(
                f"module\n\npublic import {module}.Frozen\npublic import {module}.Peer\npublic import {module}.PeerTwo\n"
                f"public import {module}.Main\npublic import {module}.sameName.{module}.Main\n")
            build(module + ".Combined", env)
            # An exclusive export fails before running search and preserves the file.
            (scratch / "Again.lean").write_text(
                "module\n\nimport HexECPPMathlib.Native\n"
                f"#ecpp_export (method := ecpp) {module}.Certificate cert for {n}\n")
            build(module + ".Again", env, expected_error="already exists")
            assert certificate.read_bytes() == frozen
            (scratch / "Editor.lean").write_text(
                "module\n\nimport HexECPPMathlib.Native\nset_option Elab.inServer true in\n"
                f"#ecpp_export (method := ecpp) {module}.EditorOutput cert for 5\n")
            build(module + ".Editor", env)
            assert not (scratch / "EditorOutput.lean").exists()
            assert not marker.exists(), "native production or frozen replay invoked GP"
            print(json.dumps({"subject": n, "seed": seed, "frozen_source_bytes": len(frozen),
                              "sha256": hashlib.sha256(frozen).hexdigest(),
                              "kernel_replay_without_search_or_gp": True}))


if __name__ == "__main__":
    main()
