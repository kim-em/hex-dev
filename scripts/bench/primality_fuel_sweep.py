#!/usr/bin/env python3
"""Measure and report the HexPrimality certificate-depth fuel policy.

The native probe times inside one process after an untimed warmup. This runner
alternates ascending and descending fuel ladders, retains every raw sample, and
requires every successful search to replay ``checkPrime`` in the probe.

Scientific run::

    python3 scripts/bench/primality_fuel_sweep.py \
      --rounds 6 --repeats 3 \
      --output reports/bench-results/hex-primality-fuel-issue-9784-chungus2.json

The companion fresh-module evidence uses the already registered end-to-end
policy suite::

    python3 scripts/bench/primality_elab_sweep.py --samples 6 \
      --shared-host --expected-host chungus2 --cpu 22 --timeout 30 \
      --warm-timeout 600 --max-pair-retries 32 \
      --output reports/bench-results/hex-primality-fuel-elab-issue-9784-chungus2.json

Use ``--report FILE`` to reproduce the native summary without measuring.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
import platform
from pathlib import Path
import shlex
import signal
import socket
import statistics
import subprocess
import sys

try:
    import idle_core
except ModuleNotFoundError:  # imported as ``scripts.bench.*`` by unit tests
    from scripts.bench import idle_core


ROOT = Path(__file__).resolve().parents[2]
PROBE = ROOT / ".lake" / "build" / "bin" / "hexprimality_fuel_probe"
FUEL_RUNGS = (0, 1, 2, 3, 4, 8, 16)
RUNTIME_BUDGET_NANOS = 5_000_000_000


@dataclass(frozen=True)
class Case:
    name: str
    n: int
    family: str
    allocation: str
    minimum_fuel: int | None
    provenance: str


CASES = (
    Case(
        "table-smooth-31",
        2_147_483_647,
        "table-smooth",
        "production",
        1,
        "2^31 - 1; n - 1 factors entirely over the committed table",
    ),
    Case(
        "table-smooth-61",
        1_945_555_039_024_054_273,
        "table-smooth",
        "production",
        1,
        "27 * 2^56 + 1; n - 1 factors entirely over the committed table",
    ),
    Case(
        "table-smooth-123",
        9_304_595_970_494_411_110_326_649_421_962_412_033,
        "table-smooth",
        "production",
        1,
        "7 * 2^120 + 1; n - 1 factors entirely over the committed table",
    ),
    Case(
        "table-smooth-256",
        93_628_759_656_736_142_393_278_101_159_368_737_990_730_026_663_232_799_828_780_155_818_898_507_169_793,
        "table-smooth",
        "production",
        1,
        "207 * 2^248 + 1; n - 1 factors entirely over the committed table",
    ),
    Case(
        "p-minus-one-friendly-20",
        1_000_003,
        "p-minus-one-friendly",
        "production",
        2,
        "n - 1 = 2 * 3 * 166667 and 166667 - 1 = 2 * 167 * 499",
    ),
    Case(
        "recursive-30",
        1_000_000_007,
        "recursively-certified",
        "production",
        3,
        "n - 1 contains 500000003, producing a three-node certificate path",
    ),
    Case(
        "rho-friendly-512",
        9_521_691_625_768_090_263_084_389_838_561_930_764_813_603_239_089_634_545_416_648_725_957_969_250_257_409_112_878_363_599_328_138_633_827_640_729_385_461_401_574_761_860_536_478_435_114_675_541_614_002_177,
        "rho-friendly",
        "elaboration",
        2,
        "100297^22 * 2^146 + 1; bounded rho discovers the above-table factor",
    ),
    Case(
        "honest-exhaustion-512",
        11_069_588_345_001_798_189_188_705_872_711_741_673_446_310_956_174_776_680_242_876_230_365_522_527_670_481_055_399_138_994_024_099_817_696_810_905_038_323_515_123_654_848_684_366_962_778_647_276_800_762_123,
        "honest-exhaustion",
        "elaboration",
        None,
        "fixed safe probable prime from the elaborator policy suite; no primality claim",
    ),
)


def git(args: list[str]) -> str:
    return subprocess.run(
        ["git", *args], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout.strip()


def lean_version() -> str:
    return subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT, check=True,
        capture_output=True, text=True,
    ).stdout.strip()


def host_state(cpu: int) -> dict:
    model = "unknown"
    try:
        for block in Path("/proc/cpuinfo").read_text().split("\n\n"):
            fields = {
                key.strip(): value
                for line in block.splitlines()
                if ":" in line
                for key, value in (line.split(":", 1),)
            }
            if fields.get("processor", "").strip() == str(cpu):
                model = fields.get("model name", "unknown").strip()
                break
    except OSError:
        pass
    try:
        pressure = Path("/proc/pressure/cpu").read_text().strip()
    except OSError:
        pressure = "unavailable"
    return {
        "cpu": cpu,
        "affinity": sorted(os.sched_getaffinity(0)),
        "cpu_model": model,
        "load_average": list(os.getloadavg()),
        "cpu_pressure": pressure,
    }


def run_checked(command: list[str], timeout: float) -> str:
    proc = subprocess.Popen(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        proc.communicate()
        raise RuntimeError(f"command timed out after {timeout}s: {shlex.join(command)}")
    if proc.returncode != 0:
        raise RuntimeError(
            f"command failed ({proc.returncode}): {shlex.join(command)}\n{stdout}{stderr}"
        )
    return stdout


def run_rung(case: Case, fuel: int, repeats: int, timeout: float) -> dict:
    output = run_checked(
        [str(PROBE), case.allocation, str(case.n), str(fuel), str(repeats)],
        timeout,
    )
    row = json.loads(output)
    row["per_call_nanos"] = row["total_nanos"] / repeats
    expected = (
        "exhausted" if case.minimum_fuel is None or fuel < case.minimum_fuel
        else "success"
    )
    if row["outcome"] != expected:
        raise RuntimeError(
            f"{case.name} at fuel {fuel}: expected {expected}, got {row['outcome']}"
        )
    if (case.family == "honest-exhaustion" and fuel >= 2
            and row["attempts"] == 0):
        raise RuntimeError(f"{case.name} did not reach bounded search at fuel {fuel}")
    if row["per_call_nanos"] > RUNTIME_BUDGET_NANOS:
        raise RuntimeError(
            f"{case.name} at fuel {fuel} exceeded the 5 s per-call budget"
        )
    return row


def fuel_ladder(default_fuel: int) -> tuple[int, ...]:
    return tuple(sorted(set((*FUEL_RUNGS, default_fuel))))


def summarize(record: dict) -> list[dict]:
    rows = []
    for case in record["cases"]:
        by_fuel = []
        for fuel_text, samples in case["samples"].items():
            per_call = [sample["per_call_nanos"] for sample in samples]
            by_fuel.append({
                "fuel": int(fuel_text),
                "outcome": samples[0]["outcome"],
                "attempts": samples[0]["attempts"],
                "median_nanos": statistics.median(per_call),
                "min_nanos": min(per_call),
                "max_nanos": max(per_call),
            })
        rows.append({
            "name": case["name"],
            "bits": case["bits"],
            "family": case["family"],
            "allocation": case["allocation"],
            "minimum_fuel": case["minimum_fuel"],
            "default_fuel": case["default_fuel"],
            "rungs": sorted(by_fuel, key=lambda row: row["fuel"]),
        })
    return rows


def print_report(record: dict) -> None:
    print("| case | bits | family | minimum | default | default outcome | default median |")
    print("|---|---:|---|---:|---:|---|---:|")
    for row in record.get("summary") or summarize(record):
        default = next(rung for rung in row["rungs"]
                       if rung["fuel"] == row["default_fuel"])
        minimum = "exhausted" if row["minimum_fuel"] is None else row["minimum_fuel"]
        print(
            f"| {row['name']} | {row['bits']} | {row['family']} | {minimum} | "
            f"{row['default_fuel']} | {default['outcome']} | "
            f"{default['median_nanos'] / 1e6:.3f} ms |"
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rounds", type=int, default=6)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--cpu", default="auto",
                        help="logical CPU to pin, or auto for an idle core")
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--allow-dirty", action="store_true")
    args = parser.parse_args()
    if args.report:
        record = json.loads(args.report.read_text())
        print_report(record)
        return 0
    if args.output is None:
        parser.error("--output is required unless --report is used")
    if args.rounds < 6 or args.rounds % 2 != 0 or args.repeats < 1:
        parser.error("--rounds must be even and at least 6; repeats must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    dirty = git(["status", "--porcelain", "--untracked-files=all"])
    if dirty and not args.allow_dirty:
        parser.error("worktree is dirty; commit first or use --allow-dirty for diagnostics")

    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    state_before = host_state(cpu)
    run_checked(["lake", "build", "hexprimality_fuel_probe"], 600.0)
    cases = []
    for case in CASES:
        default_probe = run_rung(case, 0, 1, args.timeout)
        default_fuel = default_probe["default_fuel"]
        samples: dict[str, list[dict]] = {
            str(fuel): [] for fuel in fuel_ladder(default_fuel)
        }
        ladder = fuel_ladder(default_fuel)
        for round_index in range(args.rounds):
            order = ladder if round_index % 2 == 0 else tuple(reversed(ladder))
            for fuel in order:
                sample = run_rung(case, fuel, args.repeats, args.timeout)
                sample["round"] = round_index
                sample["order"] = "ascending" if round_index % 2 == 0 else "descending"
                samples[str(fuel)].append(sample)
        cases.append({
            "name": case.name,
            "n": case.n,
            "bits": default_probe["bits"],
            "family": case.family,
            "allocation": case.allocation,
            "minimum_fuel": case.minimum_fuel,
            "default_fuel": default_fuel,
            "provenance": case.provenance,
            "samples": samples,
        })
        print(f"measured {case.name}", file=sys.stderr)

    record = {
        "schema": "hex-primality-fuel-policy-v1",
        "measurement": "warm native certificate search; counterbalanced fuel order",
        "acceptance": (
            "the probe performs one untimed same-implementation checkPrime replay "
            "for every success; expected depth thresholds are exact; honest "
            "exhaustion consumes bounded work and makes no primality claim"
        ),
        "environment": {
            "hostname": socket.gethostname(),
            "platform": platform.platform(),
            "python": platform.python_version(),
            "commit": git(["rev-parse", "HEAD"]),
            "dirty": bool(dirty),
            "dirty_status": dirty,
            "lean": lean_version(),
            "command": shlex.join(sys.argv),
            "state_before": state_before,
            "state_after": host_state(cpu),
        },
        "config": {
            "rounds": args.rounds,
            "repeats": args.repeats,
            "base_fuel_rungs": list(FUEL_RUNGS),
            "policy_rung": "defaultPrimeFuel n",
            "runtime_budget_nanos_per_call": RUNTIME_BUDGET_NANOS,
            "runtime_budget_source": "HexPrimality benchmark maxSecondsPerCall",
            "elaboration_budget_nanos_per_fresh_module": 10_000_000_000,
            "elaboration_budget_source": "HexPrimality positive-certificate policy",
            "timeout_seconds": args.timeout,
            "timeout_cleanup": "SIGKILL spawned process group",
            "round_orders": [
                "ascending" if index % 2 == 0 else "descending"
                for index in range(args.rounds)
            ],
        },
        "cases": cases,
    }
    record["summary"] = summarize(record)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print_report(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
