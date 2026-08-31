#!/usr/bin/env python3
"""Inclusive phase audit for HexBerlekampZassenhaus complexity modes.

The four public-factor cases use the production `factorPhaseProfile` service.
The precision/local case uses `precisionLocalPhaseProfile`, which times every
operation in that benchmark body and records that no lattice basis reduction
is executed. Each saved profile is one complete median-total execution, so its
inclusive phase durations belong to the same call.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import statistics
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

import idle_core  # noqa: E402
from factor_sweep import HEX_SERVICE, Service, env_block  # noqa: E402


def multiply(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def split_poly(roots: list[int]) -> list[int]:
    result = [1]
    for root in roots:
        result = multiply(result, [-root, 1])
    return result


CASES = (
    {
        "benchmark": "runFactorChecksum",
        "former_parameter": 24,
        "request": {"coeffs": split_poly(list(range(1, 26)))},
        "entry": "factorPhaseProfile",
    },
    {
        "benchmark": "runFactorFallbackProbeChecksum",
        "former_parameter": 24,
        "request": {"coeffs": split_poly(list(range(1, 25)))},
        "entry": "factorPhaseProfile",
    },
    {
        "benchmark": "runFactorCompareChecksum",
        "former_parameter": 4,
        "request": {"coeffs": split_poly(list(range(1, 6)))},
        "entry": "factorPhaseProfile",
    },
    {
        "benchmark": "runFactorDegreeHeightChecksum",
        "former_parameter": {"degree": 6, "height": 32},
        "request": {"coeffs": split_poly([33 * i for i in range(1, 7)])},
        "entry": "factorPhaseProfile",
    },
    {
        "benchmark": "runFastPathPrecisionLocalChecksum",
        "former_parameter": {
            "degree": 8,
            "height": 32,
            "precision": 128,
            "localFactorCount": 8,
        },
        "request": {
            "coeffs": split_poly([33 * i for i in range(1, 9)]),
            "height": 32,
            "precision": 128,
            "localFactorCount": 8,
        },
        "entry": "precisionLocalPhaseProfile",
    },
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def total_nanos(profile: dict) -> int:
    return profile["phases"]["total"]["nanos"]


def measure(service: Service, request: dict, warmup: int, repeats: int,
            cutoff: float) -> dict:
    for _ in range(warmup):
        reply, _ = service.call(request, cutoff)
        if reply is None or not reply.get("ok"):
            raise RuntimeError(f"profile warmup failed: {reply}")
    profiles = []
    for _ in range(repeats):
        reply, _ = service.call(request, cutoff)
        if reply is None or not reply.get("ok"):
            raise RuntimeError(f"profile measurement failed: {reply}")
        profiles.append(reply["result"])
    totals = [total_nanos(profile) for profile in profiles]
    median = int(statistics.median(totals))
    chosen = min(profiles, key=lambda profile: abs(total_nanos(profile) - median))
    return {
        "runs": repeats,
        "total_nanos_min": min(totals),
        "total_nanos_median": median,
        "total_nanos_max": max(totals),
        "profile": chosen,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cpu", default="auto")
    parser.add_argument("--warmup", type=int, default=1)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--cutoff", type=float, default=30.0)
    args = parser.parse_args()

    if not HEX_SERVICE.exists():
        raise SystemExit(
            f"{HEX_SERVICE} not built; run `lake build hexbz_factor_service`")
    cpu = idle_core.resolve(args.cpu)
    idle_core.pin_self(cpu)
    services = {
        entry: Service([str(HEX_SERVICE), "--entry", entry])
        for entry in {case["entry"] for case in CASES}
    }
    try:
        rows = []
        for case in CASES:
            print(f"profiling {case['benchmark']}", file=sys.stderr)
            measured = measure(
                services[case["entry"]], case["request"], args.warmup,
                args.repeats, args.cutoff)
            rows.append({
                "benchmark": case["benchmark"],
                "former_parameter": case["former_parameter"],
                "entry": case["entry"],
                "input_coefficients": case["request"]["coeffs"],
                **measured,
            })
    finally:
        for service in services.values():
            service.kill()

    output = {
        "schema": "hex-bz-complexity-phase-audit-v1",
        "environment": env_block(HEX_SERVICE.name),
        "cpu_affinity": cpu,
        "config": {
            "warmup": args.warmup,
            "repeats": args.repeats,
            "cutoff_seconds": args.cutoff,
            "selection": "whole execution nearest median total",
        },
        "executable_sha256": sha256(HEX_SERVICE),
        "cases": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(args.output)


if __name__ == "__main__":
    main()
