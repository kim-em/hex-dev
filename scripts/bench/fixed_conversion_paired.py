#!/usr/bin/env python3
"""Measure existing API anchors before/after certified isolation reuse.

Both directories contain frozen executables, source snapshots and metadata.json.
Registered trial-major blocks alternate adjacent AB/BA arms. Keep every completed arm;
do not filter host activity, retry failures or fit a complexity model.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease

FAMILIES = {"Add": [2, 4, 8], "Sqrt": [2, 4, 8]}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_tower_row(row, target, commit):
    if (row["kind"] != "fixed" or row["function"] != target or row["env"]["git_commit"] != commit or row["env"]["git_dirty"]
            or row["budget_truncated"] or not row["hashes_agree"]
            or row["observed_hash"] != "0x1" or row["expected_hash_check"]["status"] != "match"):
        raise ValueError("tower result is not bound to its successful source and complete consumer")
    config = row["config"]
    if (config["repeats"] != 1 or config["min_total_seconds"] != .5
            or config["warmup_first_iter"] is not True or config["max_seconds_per_call"] != 120):
        raise ValueError("tower fixed-call protocol differs")
    points = row["points"]
    if (len(points) != 1 or points[0]["status"] != "ok" or points[0]["result_hash"] != "0x1"
            or type(points[0]["inner_repeats"]) is not int or points[0]["inner_repeats"] <= 0
            or type(points[0]["total_nanos"]) is not int or points[0]["total_nanos"] <= 0):
        raise ValueError("tower fixed batch is incomplete")
    return points[0]["total_nanos"] / points[0]["inner_repeats"] / 1e6


def check_tower_cohort(sources):
    left,right=(sources[arm]["linked_objects"] for arm in ("Before","After"))
    allowed={".lake/build/ir/HexRealClosure/"+name+".c.o.export"
             for name in ("RootOrder","Trivial","TrivialMeasurements")}
    if left.keys()!=right.keys():
        raise ValueError("linked object sets differ")
    changed=set()
    for name,before in left.items():
        after=right[name]
        if before["c_sha256"]==after["c_sha256"]:
            if before["sha256"]!=after["sha256"]:
                raise ValueError("unchanged C has different compiled objects: "+name)
        else:
            changed.add(name)
            if (before.get("compiler")!=sources["Before"]["compiler"]
                    or after.get("compiler")!=sources["After"]["compiler"]
                    or before.get("command")!=after.get("command")):
                raise ValueError("changed C was not built with matched compiler commands: "+name)
    if changed!=allowed:
        raise ValueError("generated C differences differ from the registered compiler propagation")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--conversion-only", action="store_true",
                        help="Measure the existing fixed-field conversion anchor instead of scalar consumers")
    selection.add_argument("--canonical-arithmetic-only", action="store_true",
                           help="Measure existing canonical addition, multiplication and common-field powers")
    selection.add_argument("--roots-only", action="store_true",
                           help="Measure RealAlgebraicPoly.roots on existing degree families")
    selection.add_argument("--filter-roots-only", action="store_true",
                           help="Measure the existing reducible-parent X^4-1 filter control")
    selection.add_argument("--tower-order-only", action="store_true",
                           help="Compare full-word Thom reuse on the existing distinct-root generic routes")
    args = parser.parse_args()
    directories = {"Before": args.before.resolve(), "After": args.after.resolve()}
    sources = {
        arm: json.loads((directory / "metadata.json").read_text())
        for arm, directory in directories.items()
    }
    number_field = args.conversion_only or args.canonical_arithmetic_only
    executable = ("hexrealclosure_trivial_bench" if args.tower_order_only else
                  "hexnumberfield_bench" if number_field else "hexrealalgebraic_bench")
    bench = ("bench/HexRealClosure/TrivialMeasurements.lean" if args.tower_order_only else
             "bench/HexNumberField/Bench.lean" if number_field else "bench/HexRealAlgebraic/Bench.lean")
    trials = 6 if args.tower_order_only else 4
    floor = "0.5" if args.tower_order_only else "0.05"
    targets = {"FixedConversion": "Hex.NumberFieldBench.runQAdjoinCanonical",
               "CanonicalAdd": "Hex.NumberFieldBench.runAlgebraicAdd",
               "CanonicalMul": "Hex.NumberFieldBench.runAlgebraicMul",
               "CommonPowers": "Hex.NumberFieldBench.runCommonPowers"}
    families = ({"Rational": [2, 4, 6, 8], "Quadratic": [2, 4, 6, 8]} if args.tower_order_only else
                {"FixedConversion": [2]} if args.conversion_only else
                {"CanonicalAdd": [4], "CanonicalMul": [2], "CommonPowers": [16]}
                if args.canonical_arithmetic_only else {"FilterRoots": [4]}
                if args.filter_roots_only else
                {"RationalRoots": [2, 4, 8], "QuadraticRoots": [1, 2, 4]}
                if args.roots_only else FAMILIES)
    if sources["Before"]["sources"][bench] != sources["After"]["sources"][bench]:
        raise SystemExit("Benchmark source differs between compiled arms")
    executables = {}
    for arm, metadata in sources.items():
        if metadata["status"]:
            raise SystemExit(f"{arm} was compiled from a dirty source checkout")
        binary = metadata["binaries"][executable]
        executables[arm] = Path(binary["path"])
        if digest(executables[arm]) != binary["sha256"]:
            raise SystemExit(f"Frozen {arm} executable hash changed")
        for name, expected in metadata["sources"].items():
            snapshot = directories[arm] / (name.replace("/", "-") + ".txt")
            if digest(snapshot) != expected:
                raise SystemExit(f"Source snapshot changed: {arm} {name}")

        if args.tower_order_only:
            for name, expected in metadata["artifacts"].items():
                if Path(name).name != name or digest(directories[arm]/name) != expected:
                    raise RuntimeError("frozen artifact changed: " + name)

    def check_sources():
        if not args.tower_order_only:
            return
        for arm, source in sources.items():
            cwd = Path(source["cwd"])
            def git(*argv):
                return subprocess.check_output(["git", *argv], cwd=cwd, text=True).strip()
            if (source.get("freeze_status") != "frozen" or git("status", "--porcelain")
                    or git("rev-parse", "HEAD") != source["commit"]):
                raise RuntimeError(f"{arm} frozen source changed")
        allowed = {"HexRealClosure/RootOrder.lean", "HexRealClosure/RootOrderTests.lean",
                   "adapters/HexRealClosureTheory/RootOrder.lean",
                   "adapters/HexRealClosureTheory/TrivialTowerTests.lean"}
        changed = set(subprocess.check_output(
            ["git", "diff", "--name-only", sources["Before"]["commit"], sources["After"]["commit"],
             "--", "*.lean", "lake-manifest.json", "lean-toolchain"], cwd=ROOT, text=True).splitlines())
        if changed != allowed:
            raise RuntimeError("compiled source differences do not match the registered comparison")
        if sources["Before"]["lean_bench_pin"] != sources["After"]["lean_bench_pin"]:
            raise RuntimeError("LeanBench pins differ")
        own = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        if (subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip()
                or any(m["tooling_commit"] != own for m in sources.values())):
            raise RuntimeError("collector differs from the frozen tooling")
        return sorted(changed)
    source_differences = check_sources()
    if args.tower_order_only:
        check_tower_cohort(sources)
    output = args.output.resolve()
    if args.tower_order_only and any(output == Path(m["cwd"]) or Path(m["cwd"]) in output.parents for m in sources.values()):
        raise RuntimeError("capture outside the frozen source checkouts")
    output.mkdir(parents=True, exist_ok=False)
    for arm, directory in directories.items():
        for snapshot in directory.glob("*.txt"):
            shutil.copyfile(snapshot, output / f"{arm}-{snapshot.name}")
    shutil.copyfile(Path(__file__), output / "collector.py")
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {
        "sources": sources,
        "status": "running", "capture_root": str(output),
        "compiled_source_differences": source_differences,
        "panic_abort": bool(args.tower_order_only),
        "affinity": sorted(os.sched_getaffinity(0)),
        "families": families,
        "trials": list(range(trials)),
        "mode": "tower-order" if args.tower_order_only else "legacy",
        "floor_seconds": float(floor),
        "collector_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "cpu": cpu,
        "host": os.uname().nodename,
        "load_start": os.getloadavg(),
        "start": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "schedule": f"{trials} trial-major blocks, adjacent Before/After arms, alternating AB/BA",
        "boundary": ("Existing unchanged benchmark input; paired result agreement, "
                     "registration has no expected hash. " if args.filter_roots_only else
                     "Existing unchanged benchmark input and expected result fingerprint. ") +
                    "Preparation and separate warmup excluded; registered caps unchanged. "
                    f"Each arm uses one fixed batch with a {float(floor)*1000:g} ms floor. Descriptive comparison, "
                    "no scientific mode admission or portable timing budget.",
        "arms": [],
    }

    def save() -> None:
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")

    save()
    try:
        for trial in range(trials):
            order = ["Before", "After"] if trial % 2 == 0 else ["After", "Before"]
            for operation, sizes in families.items():
                for size in sizes:
                    for arm in order:
                        label = f"{operation}-{size}-{trial}-{arm}"
                        target = (f"Hex.RealClosure.TrivialMeasurements.{operation}{size}.generic" if args.tower_order_only else
                                  targets[operation] if number_field else
                                  "Hex.RealAlgebraicBench.runFilterRoots" if args.filter_roots_only else
                                  f"Hex.RealAlgebraicBench.run{operation}{size}" if args.roots_only
                                  else f"Hex.RealAlgebraicScaling.run{operation}{size}")
                        command = [
                            str(executables[arm]), "run",
                            target,
                            "--repeats", "1", "--min-total-seconds", floor,
                            "--export-file", str(output / f"{label}.json"),
                        ]
                        metadata["active_command"] = command
                        save()
                        load_before = os.getloadavg()
                        start = time.monotonic()
                        with (output / f"{label}.log").open("w") as log:
                            result = subprocess.run(command,
                                                    cwd=sources[arm]["cwd"] if args.tower_order_only else ROOT,
                                                    env={**os.environ, "LEAN_ABORT_ON_PANIC": "1"} if args.tower_order_only else None,
                                                    stdout=log, stderr=subprocess.STDOUT, check=False,
                                                    timeout=3600 if args.tower_order_only else None)
                        metadata["arms"].append({
                            "operation": operation, "size": size, "trial": trial,
                            "arm": arm, "order": order, "command": command,
                            "exit_code": result.returncode,
                            "load_before": load_before, "load_after": os.getloadavg(),
                            "elapsed_seconds": time.monotonic() - start,
                            "output": f"{label}.json",
                        })
                        metadata.pop("active_command", None)
                        save()
                        print(label, "exit", result.returncode, flush=True)
                        if args.tower_order_only:
                            if result.returncode:
                                raise RuntimeError("failed arm retained: " + label)
                            row = json.loads((output / f"{label}.json").read_text())["results"]
                            if len(row) != 1:
                                raise RuntimeError("unexpected benchmark result count")
                            validate_tower_row(row[0], target, sources[arm]["commit"])
        check_sources()
        metadata["status"] = "completed"
    except BaseException as error:
        metadata.update(status="failed", error=str(error))
        raise
    finally:
        metadata["load_end"] = os.getloadavg()
        metadata["binaries_unchanged"] = all(
            digest(executables[arm]) == sources[arm]["binaries"][executable]["sha256"]
            for arm in executables
        )
        metadata["artifacts"] = {
            path.name: digest(path) for path in output.iterdir()
            if path.is_file() and path.name != "metadata.json"
        }
        save()
        lease.close()


if __name__ == "__main__":
    main()
