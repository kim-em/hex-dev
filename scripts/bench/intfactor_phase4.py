#!/usr/bin/env python3
"""Collect and reproduce the HexIntFactor Phase-4 evidence package.

The scientific run pins itself and every child to one idle logical CPU, runs
all registered ``hexintfactor_bench`` targets at their declared settings, then
measures the two informational external comparisons:

* PARI ``factor`` on the full balanced-semiprime ladder. PARI's own wall clock
  times a calibrated batch inside one GP process, excluding GP startup.
* GMP-ECM stage 1 with ``B1=1000`` and ``sigma=7`` on the exact inputs used by
  the Lean ECM registrations. A calibrated multi-input batch keeps one process
  alive; a same-command batch of 15 records the remaining protocol floor.

Examples::

    python3 scripts/bench/intfactor_phase4.py --pari /path/to/gp \
      --ecm /path/to/ecm --output reports/bench-results/hex-int-factor.json
    python3 scripts/bench/intfactor_phase4.py --report \
      reports/bench-results/hex-int-factor.json
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
except ModuleNotFoundError:  # imported as ``scripts.bench.*`` by tests
    from scripts.bench import idle_core


ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / ".lake" / "build" / "bin" / "hexintfactor_bench"

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
    (72, 2_362_266_098_603_427_230_429),
    (76, 37_781_266_112_080_922_588_887),
    (80, 604_472_739_136_871_618_122_723),
)


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def host_state(cpu: int) -> dict:
    model = "unknown"
    for block in Path("/proc/cpuinfo").read_text().split("\n\n"):
        fields = dict(line.split(":", 1) for line in block.splitlines() if ":" in line)
        if fields.get("processor", "").strip() == str(cpu):
            model = fields.get("model name", "unknown").strip()
            break
    pressure = Path("/proc/pressure/cpu")
    return {
        "cpu": cpu,
        "affinity": sorted(os.sched_getaffinity(0)),
        "cpu_model": model,
        "load_average": list(os.getloadavg()),
        "cpu_pressure": pressure.read_text().strip() if pressure.exists() else "unavailable",
    }


def run(command: list[str], *, stdin: str | None = None, timeout: float = 30.0) -> subprocess.CompletedProcess:
    return subprocess.run(
        command, cwd=ROOT, input=stdin, check=True, capture_output=True,
        text=True, timeout=timeout,
    )


def median_row(samples: list[float]) -> dict:
    return {
        "samples_nanos": samples,
        "median_nanos": statistics.median(samples),
        "min_nanos": min(samples),
        "max_nanos": max(samples),
    }


def combined_output(command: list[str]) -> str:
    proc = run(command)
    return (proc.stdout + proc.stderr).strip()


def bench_result(export: dict, function: str) -> dict:
    return next(row for row in export["results"] if row["function"] == function)


def lean_medians(export: dict, function: str) -> dict[int, float]:
    row = bench_result(export, function)
    if row.get("trial_summaries"):
        return {
            item["param"]: item["median_per_call_nanos"]
            for item in row["trial_summaries"]
        }
    grouped: dict[int, list[float]] = {}
    for point in row["points"]:
        if point["status"] == "ok":
            grouped.setdefault(point["param"], []).append(point["per_call_nanos"])
    return {param: statistics.median(values) for param, values in grouped.items()}


def gp_batch(gp: str, n: int, repeats: int, timeout: float) -> tuple[float, int]:
    program = (
        f"my(t=getwalltime());my(f);for(i=1,{repeats},f=factor({n}));"
        "print(getwalltime()-t);print(factorback(f));quit\n"
    )
    output = run([gp, "-fq"], stdin=program, timeout=timeout).stdout.splitlines()
    values = [line.strip() for line in output if line.strip()]
    if len(values) != 2:
        raise RuntimeError(f"unexpected GP reply for {n}: {output!r}")
    return float(values[0]) * 1_000_000.0 / repeats, int(values[1])


def measure_pari(gp: str, n: int, rounds: int, timeout: float) -> dict:
    repeats = 1
    while True:
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI factor product mismatch at {n}: {product}")
        if per_call * repeats >= 50_000_000 or repeats >= 1 << 20:
            break
        repeats *= 2
    samples = []
    for _ in range(rounds):
        per_call, product = gp_batch(gp, n, repeats, timeout)
        if product != n:
            raise RuntimeError(f"PARI factor product mismatch at {n}: {product}")
        samples.append(per_call)
    return {"batch_repeats": repeats, **median_row(samples)}


def ecm_batch(ecm: str, n: int, repeats: int, timeout: float) -> tuple[float, list[list[int]]]:
    started = time.monotonic_ns()
    proc = subprocess.run(
        [ecm, "-q", "-sigma", "7", "1000"], cwd=ROOT,
        input=f"{n}\n" * repeats,
        capture_output=True, text=True, timeout=timeout,
    )
    elapsed = float(time.monotonic_ns() - started) / repeats
    # GMP-ECM uses exit codes to classify the factor it found (8 for the
    # trivial/overhead input, 14 for a factor found in stage 1).
    if proc.returncode not in (0, 2, 6, 8, 10, 14):
        raise RuntimeError(
            f"GMP-ECM failed ({proc.returncode}) at {n}: {proc.stderr}"
        )
    outputs = [
        [int(token) for token in line.split() if token.isdigit()]
        for line in proc.stdout.splitlines() if line.strip()
    ]
    if len(outputs) != repeats:
        raise RuntimeError(
            f"GMP-ECM returned {len(outputs)} rows for {repeats} inputs at {n}"
        )
    return elapsed, outputs


def measure_ecm(ecm: str, n: int, rounds: int, timeout: float) -> dict:
    repeats = 1
    while True:
        per_call, outputs = ecm_batch(ecm, n, repeats, timeout)
        if any((row != [15] if n == 15 else len(row) != 2 or row[0] * row[1] != n)
               for row in outputs):
            raise RuntimeError(f"GMP-ECM factor mismatch at {n}: {outputs[:3]}")
        if per_call * repeats >= 50_000_000 or repeats >= 1 << 20:
            break
        repeats *= 2
    samples = []
    output_example = outputs[0]
    for _ in range(rounds):
        per_call, outputs = ecm_batch(ecm, n, repeats, timeout)
        if any((row != [15] if n == 15 else len(row) != 2 or row[0] * row[1] != n)
               for row in outputs):
            raise RuntimeError(f"GMP-ECM factor mismatch at {n}: {outputs[:3]}")
        samples.append(per_call)
    return {
        "batch_repeats": repeats,
        **median_row(samples),
        "output_example": output_example,
    }


def print_report(record: dict) -> None:
    export = record["benchmark_export"]
    print("| target | verdict | selected mode |")
    print("|---|---|---|")
    for row in export["results"]:
        if row["kind"] == "fixed":
            verdict = f"median {row['median_nanos'] / 1e6:.3f} ms; hashes agree={row['hashes_agree']}"
            mode = "3 (fixed policy schedule)"
        else:
            verdict = row["verdict"]
            mode = ("1" if verdict == "consistent_with_declared_complexity"
                    else "2 (manual upper bound)")
        print(f"| `{row['function'].rsplit('.', 1)[-1]}` | {verdict} | {mode} |")
    print("\n| bits | Lean factor | PARI factor | Lean / PARI |")
    print("|---:|---:|---:|---:|")
    for row in record["comparisons"]["pari"]:
        print(f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
              f"{row['pari']['median_nanos']/1e6:.3f} ms | {row['lean_over_pari']:.2f}x |")
    overhead = record["comparisons"]["gmp_ecm_overhead"]["median_nanos"]
    print(f"\nGMP-ECM batched protocol floor: {overhead/1e6:.3f} ms/input\n")
    print("| bits | Lean ECM | GMP-ECM raw | GMP-ECM adjusted | Lean / adjusted |")
    print("|---:|---:|---:|---:|---:|")
    for row in record["comparisons"]["gmp_ecm"]:
        print(f"| {row['bits']} | {row['lean_nanos']/1e6:.3f} ms | "
              f"{row['ecm']['median_nanos']/1e6:.3f} ms | "
              f"{row['adjusted_nanos']/1e6:.3f} ms | {row['lean_over_adjusted']:.2f}x |")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--pari", default="gp")
    parser.add_argument("--ecm", default="ecm")
    parser.add_argument("--cpu", default="auto")
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--allow-dirty", action="store_true")
    args = parser.parse_args()
    if args.report:
        print_report(json.loads(args.report.read_text()))
        return 0
    if args.output is None:
        parser.error("--output is required unless --report is used")
    if args.rounds < 5 or args.rounds % 2 == 0 or args.timeout <= 0:
        parser.error("--rounds must be odd and at least 5; --timeout must be positive")
    dirty = git("status", "--porcelain", "--untracked-files=all")
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty for diagnostics")

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    state_before = host_state(cpu)
    run(["lake", "build", "hexintfactor_bench"], timeout=max(300.0, args.timeout))
    if not BENCH.exists():
        raise RuntimeError(f"benchmark executable missing after build: {BENCH}")
    with tempfile.TemporaryDirectory(prefix="hex-int-factor-") as directory:
        temp = Path(directory)
        export_path = Path(directory) / "bench.json"
        command = [str(BENCH), "run", "--filter", "Hex.IntFactorBench",
                   "--export-file", str(export_path)]
        run(command, timeout=max(600.0, args.timeout))
        export = json.loads(export_path.read_text())
        compare_exports = {}
        compare_groups = {
            "ecm_rho_word": ("Hex.IntFactorBench.runEcmWord",
                             "Hex.IntFactorBench.runEcmRhoWord"),
            "ecm_rho_nat": ("Hex.IntFactorBench.runEcmNat",
                            "Hex.IntFactorBench.runEcmRhoNat"),
            "power_split": ("Hex.IntFactorBench.runPowerGeneric",
                            "Hex.IntFactorBench.runPowerSplit"),
        }
        for label, functions in compare_groups.items():
            path = temp / f"{label}.json"
            run([str(BENCH), "compare", *functions, "--export-file", str(path)],
                timeout=max(600.0, args.timeout))
            compare_exports[label] = json.loads(path.read_text())

    fuel_rows = []
    for line in run([str(BENCH), "default-fuel"], timeout=max(300.0, args.timeout)).stdout.splitlines():
        n, fuel, status, attempts = line.split(",")
        fuel_rows.append({
            "n": int(n), "default_fuel": int(fuel), "status": status,
            "attempts": int(attempts),
        })

    balanced_lean = lean_medians(export, "Hex.IntFactorBench.runBalancedFactor")
    pari_rows = []
    for bits, n in BALANCED:
        pari = measure_pari(args.pari, n, args.rounds, args.timeout)
        lean = balanced_lean[bits]
        pari_rows.append({
            "bits": bits, "n": n, "lean_nanos": lean, "pari": pari,
            "lean_over_pari": lean / pari["median_nanos"],
        })
        print(f"measured PARI balanced-{bits}", file=sys.stderr)

    overhead = measure_ecm(args.ecm, 15, args.rounds, args.timeout)
    word_lean = lean_medians(export, "Hex.IntFactorBench.runEcmWord")
    nat_lean = lean_medians(export, "Hex.IntFactorBench.runEcmNat")
    ecm_rows = []
    for bits, n in ECM_CASES:
        external = measure_ecm(args.ecm, n, args.rounds, args.timeout)
        adjusted = max(1.0, external["median_nanos"] - overhead["median_nanos"])
        lean = (word_lean | nat_lean)[bits]
        ecm_rows.append({
            "bits": bits, "n": n, "lean_nanos": lean, "ecm": external,
            "adjusted_nanos": adjusted,
            "overhead_fraction": overhead["median_nanos"] / external["median_nanos"],
            "lean_over_adjusted": lean / adjusted,
        })
        print(f"measured GMP-ECM unbalanced-{bits}", file=sys.stderr)

    record = {
        "schema": "hex-int-factor-phase4/1",
        "environment": {
            "hostname": socket.gethostname(), "platform": platform.platform(),
            "python": platform.python_version(), "commit": git("rev-parse", "HEAD"),
            "dirty": bool(dirty), "dirty_status": dirty,
            "lean": run(["lake", "env", "lean", "--version"]).stdout.strip(),
            "lean_bench_sha256": sha256(BENCH),
            "pari_version": combined_output([args.pari, "--version"]).splitlines()[0],
            "ecm_config": combined_output([args.ecm, "-printconfig"]),
            "command": shlex.join(sys.argv),
            "state_before": state_before, "state_after": host_state(cpu),
        },
        "config": {
            "rounds": args.rounds, "timeout_seconds": args.timeout,
            "pari_timing": "GP getwalltime around a calibrated in-process factor batch",
            "gmp_ecm_command": f"{args.ecm} -q -sigma 7 1000",
            "gmp_ecm_overhead_input": 15,
            "gmp_ecm_timing": "calibrated multi-input batch in one process",
        },
        "benchmark_export": export,
        "policy_compares": compare_exports,
        "default_fuel_schedule": fuel_rows,
        "comparisons": {
            "pari": pari_rows,
            "gmp_ecm_overhead": overhead,
            "gmp_ecm": ecm_rows,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print_report(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
