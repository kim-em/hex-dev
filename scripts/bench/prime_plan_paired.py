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

Blocks are counterbalanced: odd blocks run before then after, even blocks after
then before, so arm and position are not confounded and a drift that favours
whichever arm runs first cancels. Each instance's ratio is the median of the
*within-block* after/before ratios, not a ratio of independently pooled medians,
so a block's own load affects both arms of that ratio equally.

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
    """One `factorPhaseProfile` pass with `binary` installed as the service.

    The core is named to the child explicitly, not just through `taskset`: the
    child's `--cpu auto` would pick its own and reset the inherited affinity,
    and two arms measured on two different cores are not a paired comparison.
    """
    shutil.copy2(binary, HEX_SERVICE)
    cmd = ["taskset", "-c", str(cpu), sys.executable,
           str(ROOT / "scripts" / "bench" / "factor_phase_profile.py"),
           "--no-counterfactual", "--no-scout", "--no-kernel", "--cpu", str(cpu),
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


def summarize(record: dict, changed=()) -> list:
    """Per-instance summary: absolute medians per arm, ratios paired by block."""
    out = []
    blocks = list(zip(record["rounds"]["before"], record["rounds"]["after"]))
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
        # Paired within-block quantities: each block contributes one ratio, so a
        # block's own load cancels instead of biasing one pooled median.
        pairs = [(bb[name], aa[name]) for bb, aa in blocks
                 if name in bb and name in aa]
        ratios = [pa["total_nanos"] / pb["total_nanos"] for pb, pa in pairs]
        saved = [pb["walk_nanos"] - pa["walk_nanos"] for pb, pa in pairs]
        out.append({
            "name": name,
            "before": b,
            "after": a,
            "blocks": len(pairs),
            "walk_saved_nanos": statistics.median(saved) if saved else 0,
            "total_ratio": (statistics.median(ratios) if ratios
                            else a["total_nanos"] / b["total_nanos"]),
            "total_ratio_min": min(ratios) if ratios else None,
            "total_ratio_max": max(ratios) if ratios else None,
            # A walk can change without changing the prime it selects or the
            # number of splits it performs -- dropping a scout does exactly
            # that -- so the caller may name the rows it changed.
            "plan_changed": (name in changed if changed else
                             (b["prime"], b["splits"]) != (a["prime"], a["splits"])),
        })
    return out


def print_table(record: dict, changed=()) -> None:
    rows = summarize(record, changed)
    rounds = len(record["rounds"]["before"])
    orders = record["config"].get("block_orders")
    how = (f"median of {rounds} counterbalanced blocks "
           f"({'/'.join(orders)})" if orders
           else f"median of {rounds} alternating rounds")
    print(f"### Paired before/after, {how}\n")
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
        how = ("named by --changed" if changed
               else "detected from the selected prime and split count")
        print(f"\nLoad control ({len(controls)} instances whose plan does not "
              f"change, {how}): {lo:.3f}x to {hi:.3f}x.")


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
    p.add_argument("--changed", default=None,
                   help="comma-separated instances whose walk the change alters, "
                        "for the load-control split; by default a row counts as "
                        "changed when its selected prime or split count moved, "
                        "which does not see a dropped scout")
    args = p.parse_args()

    changed = frozenset(n.strip() for n in (args.changed or "").split(",")
                        if n.strip())
    if args.report is not None:
        print_table(json.loads(args.report.read_text()), changed)
        return 0
    if args.before is None or args.after is None or args.output is None:
        p.error("--before, --after and --output are required unless --report")

    names = ([n.strip() for n in args.names.split(",") if n.strip()]
             if args.names else REPRESENTATIVE + CONTROLS)
    tmp = args.output.with_suffix(".round.json")
    rounds = {"before": [], "after": []}
    orders = []
    for i in range(args.rounds):
        # Counterbalanced: alternate which arm runs first in each block.
        order = (("before", args.before), ("after", args.after)) if i % 2 == 0 \
            else (("after", args.after), ("before", args.before))
        orders.append("AB" if i % 2 == 0 else "BA")
        for arm, binary in order:
            print(f"block {i + 1} ({orders[-1]}) arm {arm}", file=sys.stderr)
            rounds[arm].append(collect(run_arm(binary, names, args.cpu, tmp)))
    tmp.unlink(missing_ok=True)
    shutil.copy2(args.after, HEX_SERVICE)

    record = {
        "schema": "hexbz-prime-plan-paired/2",
        "env": env_block("hexbz_factor_service"),
        "config": {
            "rounds": args.rounds,
            "block_orders": orders,
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
    record["summary"] = summarize(record, changed)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)
    print_table(record, changed)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
