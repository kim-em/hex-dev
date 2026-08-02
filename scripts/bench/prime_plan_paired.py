#!/usr/bin/env python3
"""Paired before/after prime-walk measurement (issue #9128).

A prime-planning change moves work between the prime walk and recombination, so
the only honest comparison is one where both arms see the same machine. This
driver alternates two `hexbz_factor_service` binaries -- built from the same
worktree and differing only in the planning policy -- on the same pinned core,
several rounds each, and reports the per-instance median of each arm.

The instances whose plan does not change are the load control: their prime walk
does identical work in both arms, so whatever spread they show is the day's
noise floor and bounds what can be read into the rows that did change.

Build the two binaries first, for example::

    git stash                      # or check out the before revision
    lake build hexbz_factor_service
    cp .lake/build/bin/hexbz_factor_service /tmp/svc.before
    git stash pop
    lake build hexbz_factor_service
    cp .lake/build/bin/hexbz_factor_service /tmp/svc.after

then::

    python3 scripts/bench/prime_plan_paired.py \\
        --before /tmp/svc.before --after /tmp/svc.after \\
        --rounds 3 --output reports/bench-results/hexbz-prime-plan-paired.json

`--report` re-reads a finished record and prints the markdown table without
measuring anything.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import statistics
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from factor_sweep import HEX_SERVICE, ROOT, env_block  # noqa: E402
from factor_phase_profile import CONTROLS, REPRESENTATIVE  # noqa: E402


def fmt(nanos):
    if nanos is None:
        return "--"
    sign = "-" if nanos < 0 else ""
    n = abs(nanos)
    if n >= 1e9:
        return f"{sign}{n / 1e9:.3f} s"
    if n >= 1e6:
        return f"{sign}{n / 1e6:.3f} ms"
    if n >= 1e3:
        return f"{sign}{n / 1e3:.3f} us"
    return f"{sign}{n:.0f} ns"


def run_arm(binary: Path, names, cpu: int, out: Path) -> dict:
    """One `factorPhaseProfile` pass with `binary` installed as the service."""
    shutil.copy2(binary, HEX_SERVICE)
    cmd = ["taskset", "-c", str(cpu), sys.executable,
           str(ROOT / "scripts" / "bench" / "factor_phase_profile.py"),
           "--no-counterfactual", "--no-scout",
           "--validate-names", "cyclo_phi17",
           "--names", ",".join(names), "--output", str(out)]
    subprocess.run(cmd, cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return json.loads(out.read_text())


def collect(record: dict) -> dict:
    """Per-instance walk time, total time, selected prime and split count."""
    rows = {}
    for row in record["results"]:
        profile = row.get("phase_profile") or {}
        if profile.get("status") != "ok":
            continue
        phases = profile["profile"].get("phases") or {}
        walk = profile["profile"].get("primeWalk") or {}
        rows[row["name"]] = {
            "walk_nanos": (phases.get("primeWalk") or {}).get("nanos"),
            "total_nanos": (row.get("end_to_end") or {}).get("median_nanos"),
            "prime": walk.get("selectedPrime"),
            "splits": walk.get("retainedGoodPrimes"),
            "method": profile["profile"].get("method"),
        }
    return rows


def summarize(record: dict) -> list:
    """Per-instance medians of both arms, in the record's instance order."""
    out = []
    for name in record["config"]["names"]:
        arms = {}
        for arm in ("before", "after"):
            samples = [r[name] for r in record["rounds"][arm] if name in r]
            if not samples:
                break
            arms[arm] = {
                "walk_nanos": statistics.median(s["walk_nanos"] for s in samples),
                "total_nanos": statistics.median(s["total_nanos"] for s in samples),
                "prime": samples[0]["prime"],
                "splits": samples[0]["splits"],
                "method": samples[0]["method"],
            }
        if len(arms) != 2:
            continue
        b, a = arms["before"], arms["after"]
        out.append({
            "name": name,
            "before": b,
            "after": a,
            "walk_saved_nanos": b["walk_nanos"] - a["walk_nanos"],
            "total_ratio": a["total_nanos"] / b["total_nanos"],
            "plan_changed": (b["prime"], b["splits"]) != (a["prime"], a["splits"]),
        })
    return out


def print_table(record: dict) -> None:
    rows = summarize(record)
    rounds = len(record["rounds"]["before"])
    print(f"### Paired before/after, median of {rounds} alternating rounds\n")
    print("| instance | prime before | prime after | full splits | "
          "prime walk before | prime walk after | walk saved | total before | "
          "total after | ratio |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    saved = tb = ta = 0
    for r in rows:
        b, a = r["before"], r["after"]
        saved += r["walk_saved_nanos"]
        tb += b["total_nanos"]
        ta += a["total_nanos"]
        print(f"| `{r['name']}` | {b['prime']} | {a['prime']} | "
              f"{b['splits']} -> {a['splits']} | {fmt(b['walk_nanos'])} | "
              f"{fmt(a['walk_nanos'])} | {fmt(r['walk_saved_nanos'])} | "
              f"{fmt(b['total_nanos'])} | {fmt(a['total_nanos'])} | "
              f"{r['total_ratio']:.3f}x |")
    print(f"| **aggregate** | | | | | | {fmt(saved)} | {fmt(tb)} | {fmt(ta)} | "
          f"**{ta / tb:.4f}x** |")
    controls = [r for r in rows if not r["plan_changed"]]
    if controls:
        lo = min(r["total_ratio"] for r in controls)
        hi = max(r["total_ratio"] for r in controls)
        print(f"\nLoad control ({len(controls)} instances whose plan does not "
              f"change): {lo:.3f}x to {hi:.3f}x.")


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--before", type=Path, help="service binary for the old policy")
    p.add_argument("--after", type=Path, help="service binary for the new policy")
    p.add_argument("--rounds", type=int, default=3)
    p.add_argument("--cpu", type=int, default=0)
    p.add_argument("--names", default=None,
                   help="comma-separated instance names (default: the issue "
                        "#9127 representative set plus its controls)")
    p.add_argument("--output", type=Path, default=None)
    p.add_argument("--report", type=Path, default=None,
                   help="print the table for a finished record and exit")
    args = p.parse_args()

    if args.report is not None:
        print_table(json.loads(args.report.read_text()))
        return 0
    if args.before is None or args.after is None or args.output is None:
        p.error("--before, --after and --output are required unless --report")

    names = ([n.strip() for n in args.names.split(",") if n.strip()]
             if args.names else REPRESENTATIVE + CONTROLS)
    tmp = args.output.with_suffix(".round.json")
    rounds = {"before": [], "after": []}
    for i in range(args.rounds):
        for arm, binary in (("before", args.before), ("after", args.after)):
            print(f"round {i + 1} arm {arm}", file=sys.stderr)
            rounds[arm].append(collect(run_arm(binary, names, args.cpu, tmp)))
    tmp.unlink(missing_ok=True)
    shutil.copy2(args.after, HEX_SERVICE)

    record = {
        "schema": "hexbz-prime-plan-paired/1",
        "env": env_block("hexbz_factor_service"),
        "config": {
            "rounds": args.rounds,
            "cpu": args.cpu,
            "names": names,
            "before_sha256": subprocess.run(
                ["sha256sum", str(args.before)], capture_output=True,
                text=True).stdout.split()[0],
            "after_sha256": subprocess.run(
                ["sha256sum", str(args.after)], capture_output=True,
                text=True).stdout.split()[0],
        },
        "rounds": rounds,
    }
    record["summary"] = summarize(record)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)
    print_table(record)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
