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
import subprocess
import tempfile
import time

from check_ecpp_pari import build, scratch_modules


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--subject", type=int, default=177080666831933235355717939809840315427)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--bits", type=int, choices=(256,512), default=256)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    n, seed = args.subject, args.seed
    if args.output and args.output.exists():
        parser.error("retain previous endpoint samples")
    bits = " (bits := 512)" if args.bits == 512 else ""
    source_options = ""
    root = Path(__file__).resolve().parents[2]
    provenance = dict(source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        source_hashes={name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in
            ("HexECPPTheory/Native.lean", "HexECPPTheory/Elab.lean", "HexECPPTheory/Compact.lean",
             "scripts/ci/check_ecpp_native.py", "lean-toolchain", "lake-manifest.json")})
    measurements = []
    cpu = None
    lease = None
    if args.output:
        sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"bench"))
        from cpu_lease import cpu_lease
        cpu, lease = cpu_lease()
        os.sched_setaffinity(0, {cpu})
    def measured_build(name, env, **options):
        start = time.monotonic_ns()
        try:
            output = build(name, env, timeout=600 if args.bits == 512 else 120, **options)
        except Exception as error:
            measurements.append(dict(module=name,wall_ns=time.monotonic_ns()-start,error=str(error)))
            if args.output:
                args.output.write_text(json.dumps(dict(**provenance,cpu=cpu,host=os.uname().nodename,
                    subject=n,bits=args.bits,seed=seed,measurements=measurements),indent=2)+"\n")
            raise
        measurements.append(dict(module=name,wall_ns=time.monotonic_ns()-start,output=output))
        if args.output:
            args.output.write_text(json.dumps(dict(**provenance,cpu=cpu,host=os.uname().nodename,
                subject=n,bits=args.bits,seed=seed,measurements=measurements),indent=2)+"\n")
        return output
    try:
        with scratch_modules() as scratch:
            module = "HexECPPTheory." + scratch.name
            with tempfile.TemporaryDirectory(prefix="hex-no-gp-") as folder:
                tools = Path(folder)
                marker = tools / "invoked"
                gp = tools / "gp"
                gp.write_text(f"#!{sys.executable}\nfrom pathlib import Path\n"
                              f"Path({str(marker)!r}).touch()\nraise SystemExit(99)\n")
                gp.chmod(0o755)
                env = dict(os.environ, PATH=str(tools) + os.pathsep + os.environ["PATH"])
                (scratch / "Generate.lean").write_text(
                    "module\n\nimport HexECPPTheory.Native\n\n" + source_options +
                    f"#ecpp_export (method := ecpp){bits} (seed := {seed}) {module}.Certificate cert for {n}\n"
                    f"theorem result : Nat.Prime ({n} - 1 + 1) := by\n"
                    f"  primality? (method := ecpp){bits} (seed := {seed})\n\n#print axioms result\n"
                    f"example : Hex.Nat.Prime ({n} - 1 + 1) := by\n"
                    f"  primality? (method := ecpp){bits} (seed := {seed})\n")
                output = measured_build(module + ".Generate", env)
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
                    f"module\n\npublic import {module}.Certificate\n\n" + source_options +
                    "run_cmd do\n  if (← Lean.getEnv).contains `Hex.ECPP.Native.generate then\n    throwError \"native generation is loaded during frozen replay\"\n\n"
                    f"theorem result : Nat.Prime {n} := by\n  ecpp using {module}.Certificate.cert\n"
                    "\n#print axioms result\n"
                    f"theorem suggestedNat : Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[0].strip() + "\n\n"
                    f"theorem suggestedCore : Hex.Nat.Prime ({n} - 1 + 1) := by\n  " + suggestions[1].strip() + "\n")
                output = measured_build(module + ".Frozen", env)
                assert "[propext, Classical.choice, Quot.sound]" in " ".join(output.split()), output
                # Private theorem names may repeat across independently built modules.
                # Importing the modules together must preserve their certificate data.
                (scratch / "Peer.lean").write_text(
                    "module\n\npublic import HexECPPTheory.Compact\n\n"
                    "theorem suggestedNat : Nat.Prime (13 - 1 + 1) := by\n"
                    '  ecpp using (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                    "namespace First\nprivate theorem sameName : Nat.Prime 13 := by\n"
                    '  ecpp using (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                    "end First\nnamespace Second\nprivate theorem sameName : Nat.Prime 17 := by\n"
                    '  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n'
                    "end Second\n")
                (scratch / "PeerTwo.lean").write_text(
                    "module\n\npublic import HexECPPTheory.Compact\n\n"
                    "theorem suggestedNat : Nat.Prime (17 - 1 + 1) := by\n"
                    '  ecpp using (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n')
                # Prefix concatenation alone is ambiguous: these private theorem
                # prefixes plus module names coincide without a delimiter.
                (scratch / "Main.lean").write_text(
                    "module\n\npublic import HexECPPTheory.Compact\n\n"
                    "set_option backward.privateInPublic true\n"
                    "set_option backward.privateInPublic.warn false\n"
                    f"namespace p.sameName.{module}\n"
                    "private def sameName : Hex.ECPP.Cert :=\n"
                    '  (ecpp_cert% "13" using Hex.Nat.PrimeCert.small 13)\n'
                    "@[expose] public def certificate : Hex.ECPP.Cert := sameName\n"
                    f"end p.sameName.{module}\n")
                nested = scratch / "sameName" / Path(*module.split("."))
                nested.mkdir(parents=True)
                (nested / "Main.lean").write_text(
                    "module\n\npublic import HexECPPTheory.Compact\n\n"
                    "set_option backward.privateInPublic true\n"
                    "set_option backward.privateInPublic.warn false\n"
                    "namespace p\nprivate def sameName : Hex.ECPP.Cert :=\n"
                    '  (ecpp_cert% "17" using Hex.Nat.PrimeCert.small 17)\n'
                    "@[expose] public def certificate : Hex.ECPP.Cert := sameName\n"
                    "end p\n")
                (scratch / "Combined.lean").write_text(
                    f"module\n\npublic import {module}.Frozen\npublic import {module}.Peer\npublic import {module}.PeerTwo\n"
                    f"public import {module}.Main\npublic import {module}.sameName.{module}.Main\n"
                    f"example : Nat.Prime 13 := by ecpp using p.sameName.{module}.certificate\n"
                    "example : Nat.Prime 17 := by ecpp using p.certificate\n")
                build(module + ".Combined", env)
                # An exclusive export fails before running search and preserves the file.
                (scratch / "Again.lean").write_text(
                    "module\n\nimport HexECPPTheory.Native\n"
                    f"#ecpp_export (method := ecpp){bits} {module}.Certificate cert for {n}\n")
                measured_build(module + ".Again", env, expected_error="already exists")
                assert certificate.read_bytes() == frozen
                (scratch / "Editor.lean").write_text(
                    "module\n\nimport HexECPPTheory.Native\nset_option Elab.inServer true in\n"
                    f"#ecpp_export (method := ecpp) {module}.EditorOutput cert for 5\n")
                measured_build(module + ".Editor", env)
                assert not (scratch / "EditorOutput.lean").exists()
                (scratch / "InvalidBits.lean").write_text(
                    "module\n\nimport HexECPPTheory.Native\n"
                    f"#ecpp_export (method := ecpp) (bits := 513) {module}.InvalidOutput cert for {n}\n")
                measured_build(module + ".InvalidBits", env, expected_error="bits must be 256 or 512")
                assert not (scratch / "InvalidOutput.lean").exists()
                assert not marker.exists(), "native production or frozen replay invoked GP"
                report = {**provenance, "subject": n, "bits": args.bits, "seed": seed,
                    "frozen_source_bytes": len(frozen), "sha256": hashlib.sha256(frozen).hexdigest(),
                    "kernel_replay_without_search_or_gp": True, "cpu": cpu,
                    "host": os.uname().nodename, "loadavg": list(os.getloadavg()),
                    "measurements": measurements, "frozen_source": frozen.decode(), "suggestions": suggestions}
                if args.output:
                    args.output.write_text(json.dumps(report,indent=2)+"\n")
                print(json.dumps({k:v for k,v in report.items() if k not in ("measurements","frozen_source","suggestions")}))
    finally:
        if lease:
            lease.close()


if __name__ == "__main__":
    main()
