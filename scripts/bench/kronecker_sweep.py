#!/usr/bin/env python3
"""Six adjacent AB/BA pairs against both references, with fresh import baselines.

The candidate occupies the middle of Ring/Kronecker/Grobner blocks in odd
rounds, and Grobner/Kronecker/Ring blocks in even rounds. Thus both reference
pairs are adjacent and alternate orientation; the middle candidate sample is
shared by those two comparisons. No completed sample is discarded.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as sweep

PREFIX = "HexKroneckerMathlib.ProofProbe"
MANIFEST = ROOT / "scripts/bench/kronecker_manifest.json"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def cpu_lease():
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return cpu, lease
        except BlockingIOError:
            lease.close()
    raise RuntimeError("all measurement CPU leases are held")


def arms(case):
    return ["Ring", "Kronecker", "Grobner"] if case["accepted"] else ["Decline"]


def pairs(case):
    return [sweep.ProbePair(case["stem"] + arm,
            sweep.ProbeModule(f"{PREFIX}.{case['stem']}{arm}Baseline"),
            sweep.ProbeModule(f"{PREFIX}.{case['stem']}{arm}"), dict(case, arm=arm, fresh_module_budget_ms=case["ceiling_seconds"]*1000))
            for arm in arms(case)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--case", action="append", help="diagnostic subset, not a shipping sweep")
    parser.add_argument("--resume", action="store_true", help="retain completed samples after interruption")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    cases = [c for c in manifest["cases"] if not args.case or c["stem"] in args.case]
    spec = sweep.SweepSpec(__doc__, tuple(p for c in cases for p in pairs(c)),
        "HexKroneckerMathlibProofProbe", "hex-kronecker-sweep-v1", "paired-fresh-module-olean-wall",
        "hex-kronecker", required_samples=6, absolute_only=True,
        extra_sources=(Path("scripts/bench/kronecker_manifest.json"),
                       Path("scripts/bench/kronecker_probes.py"),
                       *(Path("bench/HexKroneckerMathlib/ProofProbe") / (p+"Profile.lean")
                         for p in manifest["profiles"])))
    sweep.validate_spec(spec)
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    environment = sweep.environment()
    hashes = sweep.source_hashes(spec, Path(__file__))
    sweep.warm_imports(spec, 1200)
    topology = sweep.cpu_topology(cpu)
    monitored = sweep.parse_cpu_list(topology.get("thread_siblings_list")) or [cpu]
    samples, profiles, segments = [], [], []
    if args.resume:
        prior = json.loads(args.output.read_text())
        changed = {p for p in prior["source_hashes"] | hashes
                   if prior["source_hashes"].get(p) != hashes.get(p)}
        if changed - {str(Path(__file__).relative_to(ROOT))}:
            raise RuntimeError(f"measured sources changed: {sorted(changed)}")
        if prior["subset"] != bool(args.case):
            raise RuntimeError("cannot change sweep scope on resume")
        samples, profiles = prior["samples"], prior["profiles"]
        segments = prior.get("segments", [dict(first_sample=0, environment=prior["environment"],
            cpu=prior["cpu"], topology=prior["topology"], source_hashes=prior["source_hashes"])])
    segments.append(dict(first_sample=len(samples), environment=environment, cpu=cpu,
        topology=topology, source_hashes=hashes))
    args.output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        summaries = {}
        for case in cases:
            by_arm = {}
            for arm in arms(case):
                rows = [r for r in samples if r["stem"] == case["stem"] and r["arm"] == arm]
                deltas = [r["delta_ns"] for r in rows if r["delta_ns"] is not None]
                by_arm[arm] = dict(samples=len(rows), completed=len(deltas),
                    median_delta_ns=statistics.median(deltas) if len(deltas) == 6 else None,
                    ceiling_pass=all(r["candidate"].get("wall_nanos", float("inf")) <=
                                     case["ceiling_seconds"]*1e9 for r in rows),
                    artifacts=sweep.artifact_sizes(f"{PREFIX}.{case['stem']}{arm}", Path("bench")))
            paired = {}
            if case["accepted"]:
                for ref in ["Ring", "Grobner"]:
                    margins = []
                    for trial in range(1, 7):
                        rows = {r["arm"]: r for r in samples if r["stem"] == case["stem"] and r["trial"] == trial}
                        if all(a in rows and rows[a]["delta_ns"] is not None for a in (ref, "Kronecker")):
                            margins.append(rows[ref]["delta_ns"] - rows["Kronecker"]["delta_ns"])
                    paired[ref] = dict(margins_ns=margins,
                        median_margin_ns=statistics.median(margins) if len(margins) == 6 else None,
                        candidate_faster=len(margins) == 6 and
                            by_arm["Kronecker"]["median_delta_ns"] < by_arm[ref]["median_delta_ns"])
            summaries[case["stem"]] = dict(case, arms=by_arm, paired=paired)
        complete = len(samples) == 6*sum(len(arms(c)) for c in cases)
        record = dict(schema=spec.schema, manifest=manifest, environment=environment,
            cpu=cpu, topology=topology, source_hashes=hashes,
            sources_unchanged=hashes == sweep.source_hashes(spec, Path(__file__)),
            subset=bool(args.case), schedule_complete=complete,
            measurement_complete=complete and all(r["delta_ns"] is not None for r in samples),
            samples=samples, profiles=profiles, segments=segments, summary=summaries,
            all_accepted_faster=complete and all(p["candidate_faster"] for s in summaries.values()
                for p in s["paired"].values()), default_chain_changed=False)
        args.output.write_text(json.dumps(record, indent=2) + "\n")

    def build(module, timeout, audit):
        observations = []
        try:
            result = sweep.build_sample(module, timeout, cpu, monitored,
                lambda _m, r: observations.append(r), retain_compiler_output=True)
            if audit and (result["axioms"] is None or set(result["axioms"]) - ALLOWED):
                raise RuntimeError(f"unapproved or missing axiom audit: {result['axioms']}")
            return dict(result, state="complete")
        except RuntimeError as exc:
            result = observations[-1] if observations else {}
            return dict(result, state=result.get("state", "failed"), error=str(exc))

    for trial in range(6):
        for case in sweep.rotate(cases, trial):
            blocks = pairs(case)
            if trial % 2:
                blocks.reverse()
            for pair in blocks:
                arm = pair.metadata["arm"]
                if any(r["stem"] == case["stem"] and r["arm"] == arm and
                       r["trial"] == trial+1 for r in samples):
                    continue
                print(f"[{trial+1}/6] {case['stem']} {arm}", flush=True)
                ordered = sweep.ordered_modules(pair, trial)
                results = {role: build(module.module, 180, role == "candidate" and case["accepted"])
                           for role, module in ordered}
                success = all(r["state"] == "complete" for r in results.values())
                samples.append(dict(stem=case["stem"], family=case["family"], arm=arm, trial=trial+1,
                    build_order=[r for r, _ in ordered], **results,
                    delta_ns=results["candidate"]["wall_nanos"]-results["reference"]["wall_nanos"] if success else None))
                save()
    save()
    lease.close()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
