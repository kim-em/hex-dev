#!/usr/bin/env python3
"""Paired before/after corpus sweep for a Hex factorization change (issue #9156).

`factor_sweep.py` measures one binary in one pass. That is the right instrument
for a durable cross-system record, and the wrong one for a before/after question:
a single pass charges whatever the host was doing to whichever arm happened to be
running, and on a shared host that is worth tens of percent on the long rows.
This driver runs the whole corpus under both binaries in counterbalanced blocks
and reports, per instance, the median of the *within-block* after/before ratios.

Blocks alternate AB and BA, so arm and position are not confounded. Each block
contributes one ratio per instance, so a block's own load affects both arms of
that ratio equally.

Coverage is reported as a set difference rather than a count, because "377 of
392 in both arms" is only reassuring if it is the same 377.

Build the two binaries first, as for `prime_plan_paired.py`, then::

    python3 scripts/bench/factor_sweep_paired.py \\
        --before /tmp/svc.before --after /tmp/svc.after --blocks 2 \\
        --output reports/bench-results/hexbz-factor-sweep-paired.json

`--report` re-reads a finished record and prints the tables without measuring.
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

# Rows this fast are dominated by protocol overhead and say nothing about a
# planning change; they are measured and reported, but excluded from the
# regression scan so its output is about the rows a reader would act on.
NOISE_FLOOR_NANOS = 2_000_000


def fmt(nanos) -> str:
    if nanos is None:
        return "--"
    n = float(nanos)
    if n >= 1e9:
        return f"{n / 1e9:.3f} s"
    if n >= 1e6:
        return f"{n / 1e6:.3f} ms"
    if n >= 1e3:
        return f"{n / 1e3:.3f} us"
    return f"{n:.0f} ns"


def run_arm(binary: Path, cpu: int, cutoff: float, out: Path) -> dict:
    """One whole-corpus `factor` sweep with `binary` installed as the service."""
    shutil.copy2(binary, HEX_SERVICE)
    cmd = ["taskset", "-c", str(cpu), sys.executable,
           str(ROOT / "scripts" / "bench" / "factor_sweep.py"),
           "--systems", "hex-factor", "--cutoff", str(cutoff),
           "--no-early-terminate", "--output", str(out)]
    subprocess.run(cmd, cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    record = json.loads(out.read_text())
    return {row["name"]: row for row in record.get("results", [])
            if row.get("system") == "hex-factor"}


def solved(rows: dict) -> set:
    return {name for name, row in rows.items() if row.get("status") == "ok"}


def summarize(record: dict) -> dict:
    """Per-instance paired ratios, and coverage as a set difference."""
    blocks = list(zip(record["blocks"]["before"], record["blocks"]["after"]))
    names = sorted({n for b, a in blocks for n in set(b) | set(a)})
    before_ok = set.intersection(*[solved(b) for b, _ in blocks])
    after_ok = set.intersection(*[solved(a) for _, a in blocks])
    rows = []
    for name in names:
        ratios, befores, afters = [], [], []
        for b, a in blocks:
            rb, ra = b.get(name), a.get(name)
            if not rb or not ra:
                continue
            if rb.get("status") != "ok" or ra.get("status") != "ok":
                continue
            nb, na = rb.get("median_nanos"), ra.get("median_nanos")
            if not nb or not na:
                continue
            ratios.append(na / nb)
            befores.append(nb)
            afters.append(na)
        if not ratios:
            continue
        rows.append({
            "name": name,
            "blocks": len(ratios),
            "before_nanos": statistics.median(befores),
            "after_nanos": statistics.median(afters),
            "ratio": statistics.median(ratios),
            "ratio_min": min(ratios),
            "ratio_max": max(ratios),
        })
    return {
        "rows": rows,
        "solved_before": sorted(before_ok),
        "solved_after": sorted(after_ok),
        "lost": sorted(before_ok - after_ok),
        "gained": sorted(after_ok - before_ok),
    }


def print_tables(record: dict, top: int) -> None:
    s = summarize(record)
    rows = sorted(s["rows"], key=lambda r: r["ratio"])
    blocks = len(record["blocks"]["before"])
    orders = "/".join(record["config"]["block_orders"])
    print(f"### Paired corpus sweep, median of {blocks} counterbalanced blocks "
          f"({orders})\n")
    print(f"Solved in every block: {len(s['solved_before'])} before, "
          f"{len(s['solved_after'])} after. "
          f"Lost: {', '.join(s['lost']) or 'none'}. "
          f"Gained: {', '.join(s['gained']) or 'none'}.\n")
    priced = [r for r in rows if r["ratio"] is not None]
    med = statistics.median(r["ratio"] for r in priced)
    tb = sum(r["before_nanos"] for r in priced)
    ta = sum(r["after_nanos"] for r in priced)
    print(f"{len(priced)} instances priced in every block. Median per-row ratio "
          f"{med:.4f}x; summed medians {fmt(tb)} to {fmt(ta)} ({ta / tb:.4f}x).\n")

    def table(title, subset):
        print(f"**{title}**\n")
        print("| instance | before | after | ratio | block spread |")
        print("|---|---:|---:|---:|---|")
        for r in subset:
            print(f"| `{r['name']}` | {fmt(r['before_nanos'])} | "
                  f"{fmt(r['after_nanos'])} | {r['ratio']:.3f}x | "
                  f"{r['ratio_min']:.3f}x to {r['ratio_max']:.3f}x |")
        print()

    table(f"{top} largest improvements", rows[:top])
    scan = [r for r in rows
            if r["ratio"] > 1.10 and r["after_nanos"] > NOISE_FLOOR_NANOS]
    if scan:
        table(f"Above 1.10x and over {fmt(NOISE_FLOOR_NANOS)}", scan)
    else:
        print(f"No instance above 1.10x costs more than "
              f"{fmt(NOISE_FLOOR_NANOS)}.\n")


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--before", type=Path)
    p.add_argument("--after", type=Path)
    p.add_argument("--blocks", type=int, default=2,
                   help="counterbalanced AB/BA blocks (default 2)")
    p.add_argument("--cutoff", type=float, default=10.0)
    p.add_argument("--cpu", type=int, default=None,
                   help="logical CPU to pin to; required unless --report")
    p.add_argument("--top", type=int, default=8)
    p.add_argument("--output", type=Path, default=None)
    p.add_argument("--report", type=Path, default=None)
    args = p.parse_args()

    if args.report is not None:
        print_tables(json.loads(args.report.read_text()), args.top)
        return 0
    if None in (args.before, args.after, args.output, args.cpu):
        p.error("--before, --after, --cpu and --output are required "
                "unless --report")

    tmp = args.output.with_suffix(".pass.json")
    blocks = {"before": [], "after": []}
    orders = []
    for i in range(args.blocks):
        order = (("before", args.before), ("after", args.after)) if i % 2 == 0 \
            else (("after", args.after), ("before", args.before))
        orders.append("AB" if i % 2 == 0 else "BA")
        for arm, binary in order:
            print(f"block {i + 1} ({orders[-1]}) arm {arm}", file=sys.stderr)
            blocks[arm].append(run_arm(binary, args.cpu, args.cutoff, tmp))
    tmp.unlink(missing_ok=True)
    shutil.copy2(args.after, HEX_SERVICE)

    record = {
        "schema": "hexbz-factor-sweep-paired/1",
        "env": env_block("hexbz_factor_service"),
        "config": {
            "blocks": args.blocks,
            "block_orders": orders,
            "cpu": args.cpu,
            "cutoff_seconds": args.cutoff,
            "before_sha256": subprocess.run(
                ["sha256sum", str(args.before)], capture_output=True,
                text=True).stdout.split()[0],
            "after_sha256": subprocess.run(
                ["sha256sum", str(args.after)], capture_output=True,
                text=True).stdout.split()[0],
        },
        "blocks": blocks,
    }
    record["summary"] = summarize(record)
    args.output.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(f"wrote {args.output}", file=sys.stderr)
    print_tables(record, args.top)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
