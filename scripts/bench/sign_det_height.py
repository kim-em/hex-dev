#!/usr/bin/env python3
"""Check the fixed-degree height ladder against its unique real root, 1."""
import argparse
import json
import math
from pathlib import Path

HEIGHTS = [64, 128, 256, 512, 1024, 2048, 4096]
PHASE_HEIGHTS = [8192, 16384, 32768, 65536, 131072, 262144, 524288]
FUNCTIONS = ("Height.runReduce", "Height.runCheck")
HASH_FIELDS = {"inputHash", "productionResultHash", "replayResultHash"}


def expected(height):
    c = 2**height - 1
    table = [[[1, 1, 1], 1]]
    return {
        "height": height, "context": 10377,
        "head": [[-1, 1], [0, 1], [0, 1], [1, 1]],
        "queries": [[[0, 1]] * degree + [[c, 1]] for degree in (2, 1, 0)],
        "table": table, "directTable": table, "fullTable": table,
        "queryCoefficientBits": c.bit_length(),
        "reducedWitnessBits": c.bit_length(),
        "directWitnessBits": (3*c*c).bit_length(),
        "querySlots": 11, "maxColumns": 3, "treeNodes": 5,
        "graphNodes": 5, "graphEdges": 4,
    }


def integer_tree(value):
    if isinstance(value, list):
        return all(integer_tree(v) for v in value)
    return type(value) is int


def validate(path):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if len(rows) != len(HEIGHTS):
        raise ValueError("incomplete height ladder")
    for row, height in zip(rows, HEIGHTS, strict=True):
        oracle = expected(height)
        if (not isinstance(row, dict) or
                set(row) != set(oracle) | HASH_FIELDS | {"reducedGraphBytes", "directGraphBytes"} or
                not all(integer_tree(v) for v in row.values()) or
                any(row[k] != v for k, v in oracle.items())):
            raise ValueError("height input, sign table or stored witness dimensions disagree")
        if (any(not 0 <= row[key] < 2**64 for key in HASH_FIELDS) or
                row["reducedGraphBytes"] <= 0 or row["directGraphBytes"] <= 0):
            raise ValueError("invalid byte size or hash")
    # The five unshared nodes have 3+1+2+1+1 query occurrences. Each
    # stores c once in the raw query and once as its preparation scale.
    # All other reduced graph literals are independent of height.
    baseline = rows[0]["reducedGraphBytes"]
    digits = len(str(2**HEIGHTS[0]-1))
    for row, height in zip(rows, HEIGHTS, strict=True):
        if row["reducedGraphBytes"] - baseline != 16*(len(str(2**height-1))-digits):
            raise ValueError("reduced byte-size differences disagree with the 16 coefficient copies")
    return len(rows)


def phase_expected(height):
    return {"height": height, "coefficient": "2^height-1", "head": "X^3-1",
            "queryDegrees": [2, 1, 0], "steps": 3, "coefficientBits": height,
            "coefficientBytes": (height+7)//8}


def validate_phases(path, *, height_sensitive=False):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if len(rows) != len(PHASE_HEIGHTS):
        raise ValueError("incomplete normalization phase ladder")
    for row, height in zip(rows, PHASE_HEIGHTS, strict=True):
        oracle = phase_expected(height)
        if (not isinstance(row, dict) or set(row) != set(oracle) | HASH_FIELDS or
                any(row[key] != value for key, value in oracle.items()) or
                any(type(row[key]) is not int or not 0 <= row[key] < 2**64
                    for key in HASH_FIELDS) or
                any(type(row[key]) is not int for key in
                    ("height", "steps", "coefficientBits", "coefficientBytes")) or
                not integer_tree(row["queryDegrees"])):
            raise ValueError("normalization phase input differs from the symbolic oracle")
    if height_sensitive and any(len({row[key] for row in rows}) != len(rows)
                                for key in HASH_FIELDS):
        raise ValueError("phase fingerprints do not distinguish the declared heights")
    return len(rows)


def validate_export(path, name, inventory, revision, toolchain):
    """Check the registered schedule and oracle-bound outputs, retaining its verdict."""
    if name not in FUNCTIONS:
        raise ValueError("unknown height operation")
    validate_phases(inventory)
    inputs = {row["height"]: row for row in
              map(json.loads, inventory.read_text().splitlines())}
    data = json.loads(path.read_text())
    if data.get("export_schema_version") != 1 or len(data.get("results", [])) != 1:
        raise ValueError("unexpected benchmark export")
    result = data["results"][0]
    if (result.get("function") != "Hex.SignDetBench." + name or
            result.get("kind") != "parametric" or result.get("complexity_formula") != "height" or
            result.get("hashable") is not True or
            result.get("budget_truncated") is not False or
            result.get("env", {}).get("git_commit") != revision or
            result.get("env", {}).get("git_dirty") is not False):
        raise ValueError("benchmark is not bound to the clean measured source")
    # lean-toolchain pins spell release tags with v; the harness omits it.
    owner, version = toolchain.strip().rsplit(":", 1)
    version = version.removeprefix("v")
    if (result.get("env", {}).get("lean_toolchain") != owner + ":" + version or
            result.get("env", {}).get("lean_version") != version):
        raise ValueError("measurement compiler differs from the source toolchain pin")
    config = result.get("config", {})
    required = {"param_floor": PHASE_HEIGHTS[0], "param_ceiling": PHASE_HEIGHTS[-1],
                "outer_trials": 6, "target_inner_nanos": 1000000000,
                "max_seconds_per_call": 10, "signal_floor_multiplier": 10,
                "cache_mode": "warm", "verdict_warmup_fraction": 0.2,
                "slope_tolerance": 0.15, "narrow_range_noise_floor": 1.5,
                "param_schedule": {"kind": "custom", "params": PHASE_HEIGHTS}}
    if any(config.get(key) != value for key, value in required.items()):
        raise ValueError("measurement changed the declared height protocol")
    points = result.get("points", [])
    if [(p.get("trial_index"), p.get("param")) for p in points] != [
            (trial, h) for trial in range(6) for h in PHASE_HEIGHTS]:
        raise ValueError("missing, extra, reordered or duplicated timing samples")
    key = "productionResultHash" if name == "Height.runReduce" else "replayResultHash"
    for point in points:
        if type(point.get("trial_index")) is not int or type(point.get("param")) is not int:
            raise ValueError("noninteger sample index")
        if (point.get("status") != "ok" or point.get("part_of_verdict") is not True or
                point.get("below_signal_floor") is not False or
                point.get("result_hash") != hex(inputs[point["param"]][key])):
            raise ValueError("failed sample or output differs from the known root table")
        nanos = point.get("per_call_nanos")
        repeats = point.get("inner_repeats")
        if (type(nanos) not in (int, float) or not math.isfinite(nanos) or nanos <= 0 or
                type(repeats) is not int or repeats <= 0):
            raise ValueError("invalid timing or repeat count")
    if result.get("verdict") not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown model verdict")
    return {key: result[key] for key in
            ("verdict", "complexity_formula", "slope", "c_min", "c_max", "advisories")}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inventory", type=Path)
    args = parser.parse_args()
    print(f"{validate(args.inventory)} height rows match the independent root/sign oracle")
