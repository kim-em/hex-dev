#!/usr/bin/env python3
"""Retain bounded Pocklington factor-policy experiments on the frozen corpus.

Cases run independently on leased CPUs. Within each case, profiles run adjacent
and their order reverses in alternate trials. All results, including operational
timeouts, remain in the report. Native checker acceptance is recorded separately
from subsequent Lean kernel replay.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import shutil
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts/bench"))
from cpu_lease import cpu_lease


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--profiles", nargs="+", required=True)
    parser.add_argument("--subjects", choices=["bottlenecks", "successes", "holdout", "tuning", "fields"],
                        default="bottlenecks")
    parser.add_argument("--mode", choices=["factor", "construct"], default="factor")
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--trials", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--seed-offset", type=int, default=0,
                        help="Hex seed is subject plus this offset; timing trials repeat that seed")
    parser.add_argument("--primecert", type=Path)
    parser.add_argument("--corpus", type=Path, help="independently frozen prime-subject corpus")
    parser.add_argument("--split", choices=["tuning", "validation", "all"], default="all")
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output already exists; retain the original experiment")
    if args.trials < 1 or args.jobs < 1 or args.timeout <= 0:
        parser.error("trials, jobs and timeout must be positive")
    if args.seed_offset < 0:
        parser.error("seed offset must be nonnegative")
    if args.corpus and args.mode != "construct":
        parser.error("custom prime corpus requires --mode construct")
    if not args.corpus and args.subjects == "bottlenecks" and args.mode != "factor":
        parser.error("bottleneck predecessors are factorization inputs, not prime subjects")
    if "primecert" in args.profiles and (args.primecert is None or args.mode != "construct"):
        parser.error("primecert requires --primecert and --mode construct")
    corpus_path = args.corpus or ROOT / "reports/ecpp/native512/corpus-v1.json"
    corpus = json.loads(corpus_path.read_text())
    if args.corpus:
        if not corpus.get("complete"):
            parser.error("custom corpus must be completely frozen")
        cases = [c for c in corpus["cases"] if args.split == "all" or c["split"] == args.split]
        if not cases or len({c["subject"] for c in cases}) != len(cases):
            parser.error("custom corpus must select nonempty, distinct subjects")
    else:
        cases = [c for c in corpus["cases"] if c["split"] ==
                 ("tuning" if args.subjects == "tuning" else "holdout")]
    if not args.corpus and args.subjects in ["successes", "bottlenecks"]:
        cases = [c for c in cases if c["id"].endswith(("ordinary-4", "difficult-0"))]
    if not args.corpus and args.subjects == "fields":
        from primality_cactus import corpus as field_corpus
        cases = [{"id": c["name"], "subject": int(c["n"])} for c in field_corpus()
                 if c["name"] in ["Curve25519", "secp256k1", "P-256", "P-384", "Curve448", "P-521"]]
    if not args.corpus and args.subjects == "bottlenecks":
        for c in cases:
            c["subject"] = (231392247121855978133901766920235943779795090217764365202095841950595408010261529694920315912705259316767035574545980825506006625180389834577710157
                            if c["id"].endswith("ordinary-4") else c["subject"]) - 1
            c["id"] += "-child-predecessor" if c["id"].endswith("ordinary-4") else "-predecessor"
    subprocess.run(["lake", "build", "hexprimality_factor_experiment"], cwd=ROOT,
                   check=True, stdout=sys.stderr)
    executable = ROOT / ".lake/build/bin/hexprimality_factor_experiment"
    sources = ["bench/HexPrimality/FactorExperiment.lean", "HexIntFactor/Construction.lean",
               "HexIntFactor/Ecm.lean", "HexIntFactor/EcmStage2.lean",
               "HexPrimality/Construction.lean"]
    report = {
        "protocol": "Fixed trial-major per-case schedule; adjacent profile arms, reverse order "
                    "in alternate trials and alternate subjects; no supplied factors; retain every result and timeout. "
                    "The previously inspected eight holdout cases are now exploratory tuning "
                    "data, not independent validation of these new policies.",
        "argv": sys.argv, "host": platform.node(), "platform": platform.platform(),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                          text=True).strip(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "corpus_sha256": hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
        "cases": cases,
        "corpus_path": str(corpus_path),
        "executable_sha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "sources": {p: (ROOT / p).read_text() for p in sources},
        "source_sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sources},
        "git_status": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT,
                                               text=True),
        "git_diff": subprocess.check_output(["git", "diff", "HEAD"], cwd=ROOT, text=True),
        "dependency_sources_sha256": {
            str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for library in ["HexArith", "HexBasic", "HexPrimality", "HexIntFactor"]
            for p in (ROOT / library).rglob("*") if p.suffix in [".lean", ".c", ".h"]},
        "driver_source": Path(__file__).read_text(),
        "loadavg_start": list(os.getloadavg()), "samples": [], "complete": False,
    }
    if args.primecert:
        upstream = args.primecert.resolve()
        report["primecert"] = {
            "path": str(upstream),
            "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=upstream,
                                               text=True).strip(),
            "source": (upstream / "scripts/prime_cert.py").read_text(),
        }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # Freeze the measured binary: later builds must not change a running trial.
    frozen = args.output.with_suffix(".exe")
    if frozen.exists():
        parser.error("frozen executable already exists")
    shutil.copyfile(executable, frozen)
    frozen.chmod(0o755)
    assert hashlib.sha256(frozen.read_bytes()).hexdigest() == report["executable_sha256"]
    executable = frozen.resolve()
    control = subprocess.run([str(executable), "construct", "baseline", "31"],
                             cwd=ROOT, capture_output=True, text=True, timeout=30)
    if control.returncode != 0 or json.loads(control.stdout).get("status") != "success":
        raise RuntimeError(f"native control failed: {control.stdout}\n{control.stderr}")
    lock = threading.Lock()

    def save():
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(args.output)

    save()

    def run_case(indexed):
        case_index, case = indexed
        cpu, lease = cpu_lease()
        try:
            for trial in range(args.trials):
                # Reverse the first block across subjects too, so a one-trial
                # coverage sweep does not always measure the same arm first.
                profiles = args.profiles if (trial + case_index) % 2 == 0 else list(reversed(args.profiles))
                for profile in profiles:
                    command = ([sys.executable, str(upstream / "scripts/prime_cert.py"),
                                str(case["subject"])] if profile == "primecert" else
                               [str(executable), args.mode, profile, str(case["subject"]),
                                str(case["subject"] + args.seed_offset)])
                    if profile != "primecert":
                        assert hashlib.sha256(executable.read_bytes()).hexdigest() == report["executable_sha256"]
                    command = ["taskset", "-c", str(cpu), *command]
                    row = {"case": case["id"], "subject": case["subject"], "trial": trial,
                           "seed": None if profile == "primecert" else case["subject"] + args.seed_offset,
                           "executable_sha256": None if profile == "primecert" else report["executable_sha256"],
                           "profile": profile, "cpu": cpu, "command": command,
                           "state": "running", "loadavg_start": list(os.getloadavg())}
                    with lock:
                        report["samples"].append(row)
                        save()
                    print(case["id"], trial, profile, "start", cpu, flush=True)
                    start = time.monotonic_ns()
                    process = subprocess.Popen(command, cwd=upstream if profile == "primecert" else ROOT,
                                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                               text=True, start_new_session=True)
                    timed_out = False
                    try:
                        stdout, stderr = process.communicate(timeout=args.timeout)
                    except subprocess.TimeoutExpired:
                        timed_out = True
                        # Terminate the owned group before reaping its leader.
                        os.killpg(process.pid, signal.SIGKILL)
                        stdout, stderr = process.communicate(timeout=10)
                    elapsed = time.monotonic_ns() - start
                    row.update(state="timeout" if timed_out else
                               "finished" if process.returncode == 0 else "error", returncode=process.returncode,
                               wall_ns=elapsed, stdout=stdout, stderr=stderr,
                               loadavg_end=list(os.getloadavg()))
                    if not timed_out and process.returncode == 0:
                        if profile == "primecert":
                            row["result"] = {"status": "generated", "kernel_replayed": False}
                            if f"Nat.Prime {case['subject']}" not in stdout:
                                row["state"] = "invalid-output"
                        else:
                            try:
                                result = json.loads(stdout)
                                assert result["subject"] == case["subject"]
                                assert result["profile"] == profile
                                row["result"] = result
                            except (ValueError, AssertionError):
                                row["state"] = "invalid-output"
                    with lock:
                        save()
                    print(case["id"], trial, profile, row["state"], round(elapsed / 1e9, 3),
                          row.get("result", {}).get("status", ""), flush=True)
        finally:
            lease.close()

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        list(executor.map(run_case, enumerate(cases)))
    report["complete"] = True
    report["loadavg_end"] = list(os.getloadavg())
    save()
    print("complete", args.output, flush=True)


if __name__ == "__main__":
    main()
