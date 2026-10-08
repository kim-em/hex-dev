#!/usr/bin/env python3
"""Check exact frozen suggestions and fresh computational replay; --gp adds live GP."""
from __future__ import annotations
import argparse
import json
from contextlib import contextmanager
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

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
def scratch_modules(library: str = "HexIntFactor"):
    with tempfile.TemporaryDirectory(prefix="ExternalScratch", dir=ROOT / library) as temp:
        path = Path(temp)
        try:
            yield path
        finally:
            for base in (ROOT / ".lake/build/lib/lean", ROOT / ".lake/build/ir"):
                shutil.rmtree(base / library / path.name, ignore_errors=True)


def check_mixed(scratch: Path, env: dict[str, str], gp: str | None, large: bool) -> None:
    module = "HexIntFactor." + scratch.name
    tests = (ROOT / "HexIntFactor/Mixed/ExportTests.lean").read_text()
    suggestions = re.findall(r"info: Try this:\n(module\n.*?⟨certificate, rfl, by decide \+kernel⟩)\n-/", tests, re.S)
    assert len(suggestions) == 2
    for name, text, checked, subject in zip(
            ("MixedComplete", "MixedPartial"), suggestions,
            ("CheckedFactorization", "CheckedPartialFactorization"), (34, 578)):
        (scratch / f"{name}.lean").write_text(text + "\n")
        build(f"{module}.{name}", env)
        (scratch / f"Use{name}.lean").write_text(
            f"module\npublic import {module}.{name}\npublic section\n"
            f"example : Hex.Nat.Mixed.{checked} {subject} := certificate_checked\n"
            "#print axioms certificate_checked\n")
        output = build(f"{module}.Use{name}", env)
        assert "does not depend on any axioms" in output or "depends on axioms: [propext]" in output, output
        (scratch / f"Wrong{name}.lean").write_text(
            f"import {module}.{name}\n"
            f"def wrong : Hex.Nat.Mixed.{checked} {subject + 1} := certificate_checked\n")
        build(f"{module}.Wrong{name}", env, "Type mismatch")
    with scratch_modules("HexIntFactorMathlib") as proof_scratch:
        # Use the correspondence itself, without evaluating a second factorization algorithm.
        (proof_scratch / "MixedProof.lean").write_text(
            f"module\npublic import {module}.MixedPartial\n"
            "public import HexIntFactorMathlib.Mixed\npublic section\n"
            "example (p : Nat) : (578 : Nat).factorization p =\n"
            "    (certificate.factors.find? fun e => e.prime == p).elim 0 (·.exponent) +\n"
            "      certificate.residual.factorization p := certificate_checked.factorization_eq p\n"
            "#print axioms Hex.Nat.Mixed.CheckedPartialFactorization.factorization_eq\n")
        output = build(f"HexIntFactorMathlib.{proof_scratch.name}.MixedProof", env)
        assert "depends on axioms: [propext, Classical.choice, Quot.sound]" in output, output
    (scratch / "MixedEditor.lean").write_text(
        "import HexIntFactor.Mixed.Export\nset_option Elab.inServer true in\n"
        "#int_factor_mixed (method := pari) (ecpp := 512) for 34\n"
        "set_option Elab.inServer true in\n"
        f"#int_factor_mixed_export {module}.MixedEditorOutput cert for 34 using ⟨34, []⟩\n")
    build(f"{module}.MixedEditor", env)
    assert not (scratch / "MixedEditorOutput.lean").exists()
    proposal = "⟨34, [(2, 1, some (.legacy (.small 2))), (17, 1, some (.ecpp Hex.Nat.Mixed.Frozen.ecpp17))]⟩"
    (scratch / "MixedExport.lean").write_text(
        "import HexIntFactor.Mixed.Export\nimport HexIntFactor.Mixed.Frozen.Small\n"
        f"#int_factor_mixed_export {module}.MixedExported cert for 34 using {proposal}\n")
    build(f"{module}.MixedExport", env)
    exported = scratch / "MixedExported.lean"
    assert exported.read_text() == suggestions[0].replace("certificate", f"{module}.MixedExported.cert") + "\n"
    build(f"{module}.MixedExported", env)
    (scratch / "MixedAgain.lean").write_text(
        "import HexIntFactor.Mixed.Export\n"
        f"#int_factor_mixed_export {module}.MixedExported cert for 34 using ⟨34, []⟩\n")
    saved = exported.read_bytes()
    build(f"{module}.MixedAgain", env, "already exists")
    assert exported.read_bytes() == saved
    # Oversized syntax is rejected before evalExpr; each unused branch is audited.
    lets = "let x : Nat := 1; " * 16
    (scratch / "MixedSyntax.lean").write_text(
        "import HexIntFactor.Mixed.Export\nopen Lean Elab Meta Command\n"
        "run_cmd liftTermElabM do\n"
        "  let e ← Term.elabTerm (← `(term| " + lets + "x)) none\n"
        "  discard <| Hex.ECPP.auditData e { maxNodes := 8 }\n")
    build(f"{module}.MixedSyntax", env, "syntax exceeds 8 nodes")
    if gp:
        real_env = dict(env, HEX_INT_FACTOR_GP=str(Path(gp).resolve()))
        (scratch / "MixedReal.lean").write_text(
            "import HexIntFactor.Mixed.Export\n"
            f"#int_factor_mixed_export (method := pari) (ecpp := 256) {module}.MixedRealCertificate cert for 72\n")
        output = build(f"{module}.MixedReal", real_env)
        assert "mixed factor:" not in output, output
        build(f"{module}.MixedRealCertificate", env)
    if large:
        import json
        plan = json.loads((ROOT / "reports/intfactor/mixed/acceptance-v1.json").read_text())
        for case, file in zip(plan["cases"][:2], ("CaseA", "CaseB")):
            frozen = (ROOT / f"HexIntFactor/Mixed/Frozen/{file}.lean").read_text()
            start = frozen.index("(Hex.Nat.Mixed.Evidence.ecpp ")
            depth = 0
            end = start
            for end in range(start, len(frozen)):
                depth += (frozen[end] == "(") - (frozen[end] == ")")
                if depth == 0:
                    break
            evidence = frozen[start:end + 1]
            n, p = case["subject"], case["base"]
            small, exponent = case["small_base"], case["small_exponent"]
            (scratch / f"Supplied{file}.lean").write_text(
                "module\npublic import HexIntFactor.Mixed.Export\npublic section\n"
                f"#int_factor_mixed for {n} using ⟨{n}, [({small}, {exponent}, "
                f"some (.legacy (.small {small}))), ({p}, 1, some {evidence})]⟩\n")
            output = build(f"{module}.Supplied{file}", env)
            match = re.search(r"Try this:\n(.*?⟨certificate, rfl, by decide \+kernel⟩)", output, re.S)
            name = {"CaseA": "caseA", "CaseB": "caseB"}[file]
            expected = frozen[frozen.index("module\n"):].strip().replace(
                f"Hex.IntFactorMixedFrozen.{name}", "certificate")
            assert match and match.group(1) == expected, file
        print("large mixed supplied constructor admission and exact suggestions passed")
    print("mixed integer factor export: exact suggestions, supplied ECPP, ordinary replay, "
          "mathematical companion, wrong subjects, syntax bounds and exclusive creation passed")



def check_process_lifetime(scratch: Path, module: str, env: dict[str, str]) -> None:
    """Held pipes must not defeat timeout, cancellation or output limits."""
    with tempfile.TemporaryDirectory(prefix="hex-factor-process-") as temp:
        folder = Path(temp)
        backend = folder / "gp"
        # An escaped descendant cannot be signalled through the owned group.
        # The release file and finite deadline prevent a leaked test process.
        backend.write_text(f"#!{sys.executable}\n" +
            "import os, sys, time\nfrom pathlib import Path\n" +
            f"folder = Path({str(folder)!r})\n" +
            "mode = os.environ['HEX_FACTOR_TEST_MODE']\n" +
            "release = folder / (mode + '-release')\n" +
            "(folder / 'request').write_text(sys.argv[5])\n" +
            "(folder / 'leader').write_text(str(os.getpid()))\n" +
            "if mode in ('timeout', 'cancel', 'stdout', 'stderr'):\n" +
            "    if os.fork() == 0:\n" +
            "        os.setsid()\n" +
            "        (folder / 'forked').touch()\n" +
            "        deadline = time.monotonic() + 5\n" +
            "        while time.monotonic() < deadline and not release.exists():\n" +
            "            time.sleep(0.02)\n" +
            "        (folder / (mode + '-released')).touch()\n" +
            "        os._exit(0)\n" +
            "    while not (folder / 'forked').exists(): time.sleep(0.001)\n" +
            "    if mode in ('stdout', 'stderr'):\n" +
            "        os.write(1 if mode == 'stdout' else 2, b'x' * 4096)\n" +
            "    time.sleep(30)\n" +
            "elif mode == 'failed':\n" +
            "    print('backend failure', file=sys.stderr)\n    sys.exit(7)\n" +
            "else:\n    print('HEX_FACTOR_BEGIN\\n12\\n2 2\\n3 1\\nHEX_FACTOR_END')\n")
        backend.chmod(0o755)
        for mode, expected in (("timeout", ".timeout"), ("cancel", ".cancelled"),
                               ("stdout", ".stdoutLimit"), ("stderr", ".stderrLimit"),
                               ("failed", '.failed 7 "backend failure\\n"'),
                               ("success", None)):
            release = folder / (mode + "-release")
            for name in ("leader", "request", "forked"):
                (folder / name).unlink(missing_ok=True)
            path = json.dumps(str(backend))
            test = "module\npublic import HexIntFactor.Pari\npublic meta import HexIntFactor.Pari\n\n"
            test += "#eval show IO Unit from do\n  let token ← IO.CancelToken.new\n"
            if mode == "cancel":
                test += "  let task ← IO.asTask (do IO.sleep 250; token.set) .dedicated\n"
            test += "  let start ← IO.monoMsNow\n"
            timeout = 500 if mode == "timeout" else 3000
            test += (f"  let result ← Hex.Nat.Pari.run 12 {{ timeoutMs := {timeout}, "
                     f"maxOutputBytes := 128, maxErrorBytes := 128 }} {path} (some token)\n")
            test += "  let elapsed := (← IO.monoMsNow) - start\n"
            if expected:
                test += f"  unless ((match result with | .error e => e == ({expected}) | _ => false) : Bool) do throw (IO.userError s!\"unexpected result: {{repr result}}\")\n"
            else:
                test += "  unless result.isOk do throw (IO.userError s!\"unexpected result: {repr result}\")\n"
            test += '  if elapsed > 2000 then throw (IO.userError s!"cleanup blocked for {elapsed}ms")\n'
            if mode == "cancel":
                test += "  discard <| IO.wait task\n"
            if mode in ("timeout", "cancel", "stdout", "stderr"):
                test += f'  unless ← System.FilePath.pathExists {json.dumps(str(folder / "forked"))} do throw (IO.userError "escaped pipe holder was not started")\n'
            if sys.platform == "linux":
                test += f'  let pid ← IO.FS.readFile {json.dumps(str(folder / "leader"))}\n'
                test += '  if ← (System.FilePath.mk s!"/proc/{pid}/stat").pathExists then throw (IO.userError "owned child is still present before Lean exits")\n'
            test += f'  IO.println s!"{mode}: {{elapsed}}ms"\n'
            (scratch / "Process.lean").write_text(test)
            try:
                output = build(module + ".Process", dict(env, HEX_FACTOR_TEST_MODE=mode))
                print(re.search(rf"{mode}: \d+ms", output)[0])
                request = Path((folder / "request").read_text())
                assert not request.exists(), f"request file leaked: {request}"
            finally:
                release.touch()
                if mode in ("timeout", "cancel", "stdout", "stderr"):
                    deadline = time.monotonic() + 1
                    while (folder / "forked").exists() and not (folder / (mode + "-released")).exists():
                        if time.monotonic() > deadline:
                            raise AssertionError("escaped test helper did not release its pipes")
                        time.sleep(0.01)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", help="also test a real GP executable")
    parser.add_argument("--large", action="store_true", help="also decode both frozen 512-bit ECPP certificates")
    args = parser.parse_args()
    if args.gp is not None and (not args.gp or not Path(args.gp).is_file() or
                                not os.access(args.gp, os.X_OK)):
        parser.error("--gp requires an existing executable")
    env = dict(os.environ, HEX_INT_FACTOR_GP="/hex-no-factorizer-on-replay")
    with scratch_modules() as scratch:
        module = "HexIntFactor." + scratch.name
        check_process_lifetime(scratch, module, env)
        # Extract the exact complete and partial suggestions pinned by #guard_msgs.
        tests = (ROOT / "HexIntFactor/ExportTests.lean").read_text()
        suggestions = re.findall(r"info: (module\n.*?⟨certificate, rfl, by decide \+kernel⟩)\n-/", tests, re.S)
        assert len(suggestions) == 3
        suggestions = suggestions[:2]
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
            assert "integer factorization:" not in output, output
            match = re.search(r"Frozen certificate:\n(.*?⟨certificate, rfl, by decide \+kernel⟩)", output, re.S)
            assert match and match.group(1) == suggestions[0]
            build(module + ".RealCertificate", env)
        check_mixed(scratch, env, args.gp, args.large)
        print("integer factor export: exact complete/partial text, exclusive creation, "
              "editor gating and fresh computational replay passed")


if __name__ == "__main__":
    main()
