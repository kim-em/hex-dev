#!/usr/bin/env python3
"""Historical full-support reference-solve and integer-check collection support.

Validators retain the original fixed schedules and declarations. The collector
entry point is retired; historical reproduction uses the recorded revision.
"""
from __future__ import annotations

import json
import math
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

PARAMS = [1, 2, 3, 4, 5]
DIMENSION_ARITIES = [1, 2, 3, 4, 5, 6]
DIMENSION_PARAMS = [3**s for s in DIMENSION_ARITIES]
TRIALS = 6
PREFIX = "Hex.SignDetBench.MaximalMatrix."
KEYS = {"runSolve": "solveResultHash", "runCheck": "checkResultHash"}
CONFIG = {"param_floor": 1, "param_ceiling": 5, "outer_trials": TRIALS,
          "param_schedule": {"kind": "custom", "params": PARAMS},
          "target_inner_nanos": 100000000, "max_seconds_per_call": 180,
          "signal_floor_multiplier": 1, "cache_mode": "warm",
          "verdict_warmup_fraction": 0.2, "slope_tolerance": 0.15,
          "narrow_range_noise_floor": 1.5}


def sweep_settings(by_dimension):
    if not by_dimension:
        return PARAMS, KEYS, CONFIG, "27^s"
    config = {**CONFIG, "param_floor": 3, "param_ceiling": 729,
              "param_schedule": {"kind": "custom", "params": DIMENSION_PARAMS}}
    keys = {"runSolveDimension": "solveResultHash", "runCheckDimension": "checkResultHash"}
    return DIMENSION_PARAMS, keys, config, "r^3"


def validate_inventory(path, *, by_dimension=False):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    arities = DIMENSION_ARITIES if by_dimension else PARAMS
    if [r.get("queries") for r in rows] != arities:
        raise ValueError("missing, extra or reordered input")
    for row, s in zip(rows, arities, strict=True):
        n = 3**s
        expected = {"queries": s, "matrixSize": n, "supportSize": n,
                    "countSum": n, "inverseIdentityScalarPairs": n**3,
                    "inverseBits": s+1, "denominatorBits": s+1,
                    "valuesBits": n.bit_length()}
        if any(type(row.get(k)) is not int or row[k] != v for k, v in expected.items()):
            raise ValueError("wrong matrix dimensions, multiplicities or bit inventory")
        if row.get("matchesPolynomialSystem") is not (True if s <= 3 else None):
            raise ValueError("missing polynomial-system cross-check or invented higher-degree check")
        for key in ("inputHash", *KEYS.values()):
            if type(row.get(key)) is not int or not 0 <= row[key] < 2**64:
                raise ValueError("invalid input or result hash")
    return {r["matrixSize"] if by_dimension else r["queries"]: r for r in rows}


def validate_export(path, name, expected, revision, *, by_dimension=False):
    params, keys, config, formula = sweep_settings(by_dimension)
    export = json.loads(path.read_text())
    if export["export_schema_version"] != 1 or len(export["results"]) != 1:
        raise ValueError("wrong export schema or result count")
    r = export["results"][0]
    if (r["function"] != PREFIX+name or r["kind"] != "parametric" or
            r["hashable"] is not True or r["budget_truncated"] is not False):
        raise ValueError("wrong benchmark or truncated run")
    if r["env"]["git_commit"] != revision or r["env"]["git_dirty"] is not False:
        raise ValueError("child source revision differs")
    if any(type(r["config"].get(k)) is not type(v) or r["config"].get(k) != v
           for k, v in config.items()):
        raise ValueError("registered configuration differs")
    if r["complexity_formula"].replace(" ", "") != formula:
        raise ValueError("declared cost model differs")
    points = r["points"]
    if [(p["trial_index"], p["param"]) for p in points] != [
            (trial, s) for trial in range(TRIALS) for s in params]:
        raise ValueError("missing, duplicate or reordered sample")
    for p in points:
        if type(p["trial_index"]) is not int or type(p["param"]) is not int:
            raise ValueError("non-integer schedule index")
        if (p["status"] != "ok" or p["result_hash"] != hex(expected[p["param"]][keys[name]]) or
                p["part_of_verdict"] is not True or p["below_signal_floor"] is not False):
            raise ValueError("failed, incorrect or substituted sample")
        nanos = p["per_call_nanos"]
        if (type(nanos) not in (int, float) or not math.isfinite(nanos) or nanos <= 0 or
                type(p["inner_repeats"]) is not int or p["inner_repeats"] <= 0 or
                type(p.get("peak_rss_kb")) is not int or p["peak_rss_kb"] <= 0):
            raise ValueError("invalid timing, repeat count or resident-set observation")
        if p.get("alloc_bytes") is not None:
            raise ValueError("unexpected allocation counter; its meaning must be checked")
    if r["verdict"] not in ("consistent_with_declared_complexity", "inconclusive"):
        raise ValueError("unknown verdict")
    return {k: r[k] for k in ("verdict", "complexity_formula", "slope", "c_min", "c_max", "advisories")}


def collect(run, out, expected, revision, *, by_dimension=False):
    _, keys, _, _ = sweep_settings(by_dimension)
    records = [(name, run(name, ["run", PREFIX+name, "--export-file", str(out/(name+".json"))]))
               for name in keys]
    summary = {"observations": {}, "validation_errors": []}
    for name, code in records:
        if code not in (0, 1):
            summary["validation_errors"].append({"name": name, "exit_code": code})
        try:
            summary["observations"][name] = validate_export(out/(name+".json"), name, expected, revision, by_dimension=by_dimension)
        except (ValueError, KeyError, TypeError, IndexError, OSError) as error:
            summary["validation_errors"].append({"name": name, "error": str(error)})
    (out/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    return summary


def harness_binding():
    package = ROOT/".lake/packages/lean-bench"
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=package, text=True).strip()
    status = subprocess.check_output(["git", "status", "--porcelain"], cwd=package, text=True)
    pins = [p["rev"] for p in json.loads((ROOT/"lake-manifest.json").read_text())["packages"]
            if p["name"] in ("lean-bench", "«lean-bench»")]
    if len(pins) != 1 or pins[0] != revision or status:
        raise ValueError("harness checkout must be clean and match the manifest")
    return {"revision": revision, "manifest_revision": pins[0], "clean": True}


def main():
    print("Reference-solve scaling registrations are retired. "
          "Use sign_det_matrix_wide.py for production checker measurements; "
          "reproduce historical solve runs at their recorded source revision.", file=sys.stderr)
    raise SystemExit(2)


if __name__ == "__main__":
    main()
