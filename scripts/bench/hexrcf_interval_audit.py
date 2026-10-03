#!/usr/bin/env python3
"""Collect literal sign-entry counts with proof and audit-source provenance.

Run Lake's private-body audit, or parse a retained successful audit log. With
--expected-hashes, fail if any of the six retained proof artifacts differs.
Those hashes identify the last retained artifact for each probe, not every
timed arm. This structural inspection is separate from timing collection.
Retained-log mode cannot verify the historical build tree. It labels that
source binding as asserted; live builds capture their checkout before running.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
TARGET = "HexRCF.ProofProbe.Intervals.Audit"
MODULES = tuple(case + mode for case in ("Further", "Reciprocal", "Cubic")
                for mode in ("Query", "Horner"))
AUDIT_SOURCE = "bench/HexRCF/ProofProbe/Intervals/Audit.lean"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def collect(args: argparse.Namespace) -> None:
    measured = git("rev-parse", args.measured_commit).decode().strip()
    audit_commit = git("rev-parse", args.audit_commit).decode().strip()
    sources = [AUDIT_SOURCE, "lakefile.lean"] + [
        f"bench/HexRCF/ProofProbe/Intervals/{module}.lean" for module in MODULES]
    source_hashes = {path: digest(git("show", f"{audit_commit}:{path}"))
                     for path in sources}
    for path in sources[2:]:
        if digest(git("show", f"{measured}:{path}")) != source_hashes[path]:
            raise RuntimeError(f"audit probe source differs from measured source: {path}")
    artifact_paths = [f".lake/build/lib/lean/HexRCF/ProofProbe/Intervals/{module}{suffix}"
                      for module in MODULES for suffix in
                      (".olean", ".olean.private", ".olean.server", ".ilean")]
    before = {path: digest((ROOT / path).read_bytes()) for path in artifact_paths}
    expected_capture = None
    if args.expected_hashes:
        capture_bytes = args.expected_hashes.read_bytes()
        expected = json.loads(capture_bytes)
        expected_capture = {
            "sha256": digest(capture_bytes),
            "origin": expected.get("origin", "not recorded"),
        }
        # Accept either a standalone hash capture or a previous audit record.
        expected = expected.get("proof_artifact_sha256", expected)
        if before != expected:
            raise RuntimeError("retained proof artifacts differ from the expected capture")
    command = ["lake", "build", TARGET]
    capture = None
    if args.compiler_log:
        compiler = args.compiler_log.read_bytes()
        source_binding = "asserted-retrospectively; historical build tree was not captured"
    else:
        if git("rev-parse", "HEAD").decode().strip() != audit_commit:
            raise RuntimeError("build mode requires HEAD to equal --audit-commit")
        for path in sources:
            if digest((ROOT / path).read_bytes()) != source_hashes[path]:
                raise RuntimeError(f"uncommitted audit-source change: {path}")
        status = git("status", "--porcelain=v1", "--untracked-files=all")
        diff = git("diff", "HEAD", "--binary")
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "build-status.txt").write_bytes(status)
        (args.output / "build-diff.patch").write_bytes(diff)
        capture = {
            "head": git("rev-parse", "HEAD").decode().strip(),
            "head_tree": git("rev-parse", "HEAD^{tree}").decode().strip(),
            "status_file": "build-status.txt",
            "status_sha256": digest(status),
            "tracked_diff_file": "build-diff.patch",
            "tracked_diff_sha256": digest(diff),
        }
        source_binding = "verified audit/probe files; checkout captured before live build"
        result = subprocess.run(command, cwd=ROOT, capture_output=True)
        compiler = result.stdout + result.stderr
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "compiler.log").write_bytes(compiler)
        if result.returncode:
            raise RuntimeError("audit build failed; compiler output retained")
    log = compiler.decode()
    if "Build completed successfully" not in log or "error:" in log:
        raise RuntimeError("audit compiler log does not record a successful build")
    after = {path: digest((ROOT / path).read_bytes()) for path in artifact_paths}
    if before != after:
        raise RuntimeError("proof artifacts changed during the audit")
    rows = {}
    for line in log.splitlines():
        match = re.search(r"info: .*Audit\.lean:\d+:\d+: (\{.*\})$", line)
        if not match:
            continue
        row = json.loads(match[1])
        name = row["proof"]
        if name in rows:
            raise RuntimeError(f"duplicate audit row: {name}")
        if row["distinct_table_syntax"] != len(row["tables"]):
            raise RuntimeError(f"inconsistent table count: {name}")
        rows[name] = row
    names = [f"Hex.RCF.ProofProbe.Intervals.{module}.witness" for module in MODULES]
    if set(rows) != set(names):
        raise RuntimeError("audit log does not contain exactly the six probe proofs")
    replayed = {module: bool(re.search(r"Replayed HexRCF\.ProofProbe\.Intervals\."
                                      + module + r"\b", log)) for module in MODULES}
    data = {
        "schema": "hex-rcf-interval-sign-counts-v3",
        "measured_source_commit": measured,
        "audit_source_commit": audit_commit,
        "audit_source_tree": git("rev-parse", f"{audit_commit}^{{tree}}").decode().strip(),
        "audit_tree_binding": "Tree of the recorded audit reference commit; retained-log mode does not establish the historical build tree.",
        "audit_source_sha256": source_hashes,
        "source_binding": source_binding,
        "build_checkout_capture": capture,
        "audit_build_command": command,
        "compiler_log_sha256": digest(compiler),
        "compiler_reports_replayed_probes": replayed,
        "collector_sha256": digest(Path(__file__).read_bytes()),
        "collector_arguments": sys.argv[1:],
        "expected_artifact_capture": expected_capture,
        "proof_artifact_sha256": after,
        "proof_artifacts_unchanged_during_collection": True,
        "artifact_log_binding": (
            ("asserted for retained log; current hashes verified against supplied capture"
             if args.expected_hashes else
             "asserted for retained log; no expected artifact capture supplied")
            if args.compiler_log else "verified before and after live build"),
        "artifact_scope": "Six artifacts retained after the final timing arms; no per-arm hash claim.",
        "convention": "Distinct table syntax in each proof and reachable declarations from the same source module; imported library bodies are leaves. No physical-sharing or runtime-work claim.",
        "proofs": [rows[name] for name in names],
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "audit.json").write_text(json.dumps(data, indent=2) + "\n")
    print(args.output / "audit.json")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--measured-commit", required=True)
    parser.add_argument("--audit-commit", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--expected-hashes", type=Path)
    parser.add_argument("--compiler-log", type=Path)
    collect(parser.parse_args())
