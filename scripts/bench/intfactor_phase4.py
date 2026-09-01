#!/usr/bin/env python3
"""Collect and render reproducible HexIntFactor Phase-4 evidence.

All children run on one idle CPU. PARI uses calibrated in-process batches.
GMP-ECM uses one fixed 256-input batch shape with sigma 7, B1 1000, and B2 1
(B2 < B1 disables stage 2) for both the overhead control and every operand.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
from pathlib import Path
import shlex
import socket
import statistics
import subprocess
import sys
import tempfile
import time

try:
    import idle_core
except ModuleNotFoundError:
    from scripts.bench import idle_core


ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / ".lake" / "build" / "bin" / "hexintfactor_bench"
ECM_BATCH = 256
BALANCED = (
    (32, 4_296_195_809),
    (40, 1_099_546_267_613),
    (48, 281_475_177_027_259),
    (56, 72_057_609_069_267_727),
    (64, 18_446_744_168_197_812_149),
    (72, 4_722_366_488_642_080_239_163),
    (80, 1_208_925_819_625_624_289_983_961),
)
ECM_CASES = (
    (48, 268_436_384_306_737),
    (56, 68_719_683_059_430_703),
    (64, 17_592_238_821_149_133_773),
    (72, 2_362_258_565_959_719_996_521),
    (76, 37_796_135_460_432_195_119_879),
    (80, 604_738_165_771_235_538_626_863),
)


def run(command: list[str], *, stdin: str | None = None,
        timeout: float = 60.0) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command, cwd=ROOT, input=stdin, check=True, capture_output=True,
            text=True, timeout=timeout,
        )
    except subprocess.CalledProcessError as error:
        sys.stderr.write(error.stdout or "")
        sys.stderr.write(error.stderr or "")
        raise


def git(*args: str) -> str:
    return run(["git", *args]).stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def host_state(cpu: int) -> dict[str, object]:
    model = "unknown"
    for block in Path("/proc/cpuinfo").read_text().split("\n\n"):
        fields = dict(
            line.split(":", 1) for line in block.splitlines() if ":" in line
        )
        if fields.get("processor", "").strip() == str(cpu):
            model = fields.get("model name", "unknown").strip()
            break
    pressure = Path("/proc/pressure/cpu")
    return {
        "cpu": cpu,
        "affinity": sorted(os.sched_getaffinity(0)),
        "cpu_model": model,
        "load_average": list(os.getloadavg()),
        "cpu_pressure": (
            pressure.read_text().strip() if pressure.exists() else "unavailable"
        ),
    }


def median_row(samples: list[float]) -> dict[str, object]:
    return {
        "samples_nanos": samples,
        "median_nanos": statistics.median(samples),
        "min_nanos": min(samples),
        "max_nanos": max(samples),
    }


def result(export: dict[str, object], short_name: str) -> dict[str, object]:
    full = f"Hex.IntFactorBench.{short_name}"
    rows = export["results"]
    assert isinstance(rows, list)
    return next(row for row in rows if row["function"] == full)


def fixed_median(export: dict[str, object], short_name: str) -> float:
    return float(result(export, short_name)["median_nanos"])


def validate_export(export: dict[str, object]) -> None:
    rows = export["results"]
    assert isinstance(rows, list)
    failures: list[str] = []
    for row in rows:
        name = str(row["function"])
        if row["kind"] == "parametric":
            if row["verdict"] != "consistent_with_declared_complexity":
                failures.append(f"{name}: verdict={row['verdict']}")
        else:
            if not row["hashes_agree"]:
                failures.append(f"{name}: repeat hashes disagree")
            check = row["expected_hash_check"]
            if check["status"] != "matched":
                failures.append(f"{name}: expected hash {check['status']}")
    for bits, _ in BALANCED:
        normal = result(export, f"runBalancedFactor{bits}")
        forced = result(export, f"runBalancedForced{bits}")
        if normal["observed_hash"] != forced["observed_hash"]:
            failures.append(f"balanced-{bits}: output hashes differ")
        ratio = float(normal["median_nanos"]) / float(forced["median_nanos"])
        if ratio > 1.25:
            failures.append(f"balanced-{bits}: normal/forced={ratio:.6f} > 1.25")
    table = fixed_median(export, "runTableDispatch")
    trial = fixed_median(export, "runTableTrial")
    if result(export, "runTableDispatch")["observed_hash"] != \
            result(export, "runTableTrial")["observed_hash"]:
        failures.append("table: output hashes differ")
    if table / trial > 1.25:
        failures.append(f"table: dispatch/trial={table / trial:.6f} > 1.25")
    if failures:
        raise RuntimeError("invalid scientific export:\n  " + "\n  ".join(failures))


def gp_batch(gp: str, n: int, repeats: int,
             timeout: float) -> tuple[float, int]:
    program = (
        f"my(t=getwalltime());my(f);for(i=1,{repeats},f=factor({n}));"
        "print(getwalltime()-t);print(factorback(f));quit\n"
    )
    lines = run([gp, "-fq"], stdin=program, timeout=timeout).stdout.splitlines()
    values = [line.strip() for line in lines if line.strip()]
    if len(values) != 2:
        raise RuntimeError(f"unexpected GP reply for {n}: {lines!r}")
    return float(values[0]) * 1_000_000.0 / repeats, int(values[1])


def measure_pari(gp: str, n: int, rounds: int, timeout: float) -> dict[str, object]:
    repeats = 1
    while True:
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI product mismatch at {n}: {product}")
        if per_call * repeats >= 50_000_000 or repeats >= 1 << 20:
            break
        repeats *= 2
    samples = []
    for _ in range(rounds):
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI product mismatch at {n}: {product}")
        samples.append(per_call)
    return {"batch_repeats": repeats, **median_row(samples)}


def ecm_batch(ecm: str, n: int, timeout: float) -> tuple[float, list[list[int]]]:
    started = time.monotonic_ns()
    proc = subprocess.run(
        [ecm, "-q", "-sigma", "7", "1000", "1"], cwd=ROOT,
        input=f"{n}\n" * ECM_BATCH, capture_output=True, text=True,
        timeout=timeout,
    )
    elapsed = float(time.monotonic_ns() - started) / ECM_BATCH
    if proc.returncode not in (0, 2, 6, 8, 10, 14):
        raise RuntimeError(f"GMP-ECM failed ({proc.returncode}) at {n}: {proc.stderr}")
    outputs = [
        [int(token) for token in line.split() if token.isdigit()]
        for line in proc.stdout.splitlines() if line.strip()
    ]
    if len(outputs) != ECM_BATCH:
        raise RuntimeError(
            f"GMP-ECM returned {len(outputs)} rows, expected {ECM_BATCH}, at {n}"
        )
    return elapsed, outputs


def measure_ecm(ecm: str, n: int, rounds: int,
                timeout: float) -> dict[str, object]:
    samples: list[float] = []
    example: list[int] = []
    for _ in range(rounds):
        per_call, outputs = ecm_batch(ecm, n, timeout)
        bad = any(
            row != [n] and (len(row) != 2 or row[0] * row[1] != n)
            for row in outputs
        )
        if bad:
            raise RuntimeError(f"GMP-ECM factor mismatch at {n}: {outputs[:3]}")
        samples.append(per_call)
        example = outputs[0]
    return {
        "batch_repeats": ECM_BATCH,
        **median_row(samples),
        "output_example": example,
        "found_factor": len(example) == 2,
    }


def render(record: dict[str, object]) -> None:
    export = record["benchmark_export"]
    assert isinstance(export, dict)
    print("| target | harness result |")
    print("|---|---|")
    for row in export["results"]:
        short = row["function"].rsplit(".", 1)[-1]
        if row["kind"] == "fixed":
            text = (
                f"median {row['median_nanos'] / 1e6:.3f} ms; "
                f"expected hash {row['expected_hash_check']['status']}"
            )
        else:
            text = row["verdict"]
        print(f"| `{short}` | {text} |")
    controls = record["internal_controls"]
    print("\n| bits | normal | forced rho | normal / forced |")
    print("|---:|---:|---:|---:|")
    for row in controls["balanced"]:
        print(
            f"| {row['bits']} | {row['normal_nanos']/1e6:.3f} ms | "
            f"{row['forced_nanos']/1e6:.3f} ms | {row['ratio']:.3f}x |"
        )
    print("\n| bits | Hex factor | PARI factor | Hex / PARI |")
    print("|---:|---:|---:|---:|")
    for row in record["comparisons"]["pari"]:
        print(
            f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
            f"{row['pari']['median_nanos']/1e6:.3f} ms | "
            f"{row['lean_over_pari']:.2f}x |"
        )
    overhead = record["comparisons"]["gmp_ecm_overhead"]["median_nanos"]
    print(f"\nGMP-ECM fixed-batch protocol floor: {overhead/1e6:.3f} ms/input\n")
    print("| bits | Hex ECM | GMP raw | GMP adjusted | factor | eligible | Hex / adjusted |")
    print("|---:|---:|---:|---:|:---:|:---:|---:|")
    for row in record["comparisons"]["gmp_ecm"]:
        ratio = f"{row['lean_over_adjusted']:.2f}x" if row["eligible"] else "—"
        print(
            f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
            f"{row['ecm']['median_nanos']/1e6:.3f} ms | "
            f"{row['adjusted_nanos']/1e6:.3f} ms | "
            f"{'yes' if row['ecm']['found_factor'] else 'no'} | "
            f"{'yes' if row['eligible'] else 'no'} | {ratio} |"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--pari", default="gp")
    parser.add_argument("--ecm", default="ecm")
    parser.add_argument("--cpu", default="auto")
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=60.0)
    parser.add_argument("--allow-dirty", action="store_true")
    args = parser.parse_args()
    if args.report:
        render(json.loads(args.report.read_text()))
        return 0
    if args.output is None:
        parser.error("--output is required unless --report is used")
    if args.rounds < 5 or args.rounds % 2 == 0 or args.timeout <= 0:
        parser.error("--rounds must be odd and at least 5; --timeout must be positive")
    dirty = git("status", "--porcelain", "--untracked-files=all")
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty")

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    before = host_state(cpu)
    run(["lake", "build", "hexintfactor_bench", "HexIntFactorKernelProbe"],
        timeout=max(900.0, args.timeout))
    if not BENCH.exists():
        raise RuntimeError(f"missing benchmark executable: {BENCH}")

    with tempfile.TemporaryDirectory(prefix="hex-int-factor-") as directory:
        export_path = Path(directory) / "bench.json"
        run([
            str(BENCH), "run", "--filter", "Hex.IntFactorBench",
            "--export-file", str(export_path),
        ], timeout=max(1800.0, args.timeout))
        export = json.loads(export_path.read_text())
    validate_export(export)

    control_output = run([str(BENCH), "control-audit"], timeout=120.0).stdout
    if "failure" in control_output:
        raise RuntimeError(f"control audit failed:\n{control_output}")
    fuel_rows = []
    for line in run([str(BENCH), "default-fuel"], timeout=600.0).stdout.splitlines():
        n, fuel, status, attempts = line.split(",")
        fuel_rows.append({
            "n": int(n), "default_fuel": int(fuel), "status": status,
            "attempts": int(attempts),
        })
    if any(row["status"] != "success" for row in fuel_rows):
        raise RuntimeError("default-fuel schedule contains a failure")

    balanced_rows = []
    pari_rows = []
    for bits, n in BALANCED:
        normal = result(export, f"runBalancedFactor{bits}")
        forced = result(export, f"runBalancedForced{bits}")
        normal_ns = float(normal["median_nanos"])
        forced_ns = float(forced["median_nanos"])
        balanced_rows.append({
            "bits": bits, "n": n, "normal_nanos": normal_ns,
            "forced_nanos": forced_ns, "ratio": normal_ns / forced_ns,
            "hash": normal["observed_hash"],
        })
        pari = measure_pari(args.pari, n, args.rounds, args.timeout)
        pari_rows.append({
            "bits": bits, "n": n, "lean_nanos": normal_ns, "pari": pari,
            "lean_over_pari": normal_ns / float(pari["median_nanos"]),
        })
        print(f"measured balanced-{bits}", file=sys.stderr)

    overhead = measure_ecm(args.ecm, 15, args.rounds, args.timeout)
    overhead_ns = float(overhead["median_nanos"])
    ecm_rows = []
    for bits, n in ECM_CASES:
        external = measure_ecm(args.ecm, n, args.rounds, args.timeout)
        raw_ns = float(external["median_nanos"])
        adjusted = max(1.0, raw_ns - overhead_ns)
        fraction = overhead_ns / raw_ns
        lean_ns = fixed_median(export, f"runEcm{bits}")
        eligible = fraction <= 0.5 and raw_ns > overhead_ns
        ecm_rows.append({
            "bits": bits, "n": n, "lean_nanos": lean_ns,
            "ecm": external, "adjusted_nanos": adjusted,
            "overhead_fraction": fraction, "eligible": eligible,
            "lean_over_adjusted": lean_ns / adjusted,
        })
        print(f"measured ECM-{bits}", file=sys.stderr)

    table_dispatch = fixed_median(export, "runTableDispatch")
    table_trial = fixed_median(export, "runTableTrial")
    record = {
        "schema": "hex-int-factor-phase4/2",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git("rev-parse", "HEAD"),
            "dirty": bool(dirty), "dirty_status": dirty,
            "lean": run(["lake", "env", "lean", "--version"]).stdout.strip(),
            "lean_bench_sha256": sha256(BENCH),
            "kernel_source_sha256": sha256(ROOT / "bench/HexBench/IntFactorKernel.lean"),
            "pari_version": run([args.pari, "--version"]).stdout.splitlines()[0],
            "ecm_config": run([args.ecm, "-printconfig"]).stdout.strip(),
            "command": shlex.join(sys.argv),
            "state_before": before, "state_after": host_state(cpu),
        },
        "config": {
            "rounds": args.rounds, "timeout_seconds": args.timeout,
            "pari_timing": "GP getwalltime around a calibrated in-process factor batch",
            "gmp_ecm_command": f"{args.ecm} -q -sigma 7 1000 1",
            "gmp_ecm_batch_repeats": ECM_BATCH,
            "gmp_ecm_overhead_input": 15,
            "gmp_ecm_timing": "fixed persistent 256-input batch; B2 < B1 disables stage 2",
        },
        "benchmark_export": export,
        "control_audit": control_output.splitlines(),
        "internal_controls": {
            "table": {
                "dispatch_nanos": table_dispatch, "trial_nanos": table_trial,
                "ratio": table_dispatch / table_trial,
                "hash": result(export, "runTableDispatch")["observed_hash"],
            },
            "balanced": balanced_rows,
        },
        "default_fuel_schedule": fuel_rows,
        "comparisons": {
            "pari": pari_rows,
            "gmp_ecm_overhead": overhead,
            "gmp_ecm": ecm_rows,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    render(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
