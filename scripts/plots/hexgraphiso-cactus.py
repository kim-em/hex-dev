#!/usr/bin/env python3
"""Cactus plots for hex-graph-iso: nauty, compiled Hex, and the tactic.

Local/scheduled tooling, not merge CI. Two plots:

* ``canon`` — canonical labelling per instance over the deterministic
  families: pinned nauty 2.9.3 (in-process FFI) versus the public
  compiled ``canonicalize``. Data from ``lake exe hexgraphiso_cactus``.
* ``pairs`` — isomorphism proof obligations of known polarity: the
  pinned nauty comparator (canonical bits of both sides), the compiled
  ``isIso`` decision, and the ``graph_iso`` tactic (kernel-checked
  proof). Pair definitions come from
  ``lake exe hexgraphiso_cactus pairs`` (single source of truth); this
  script generates one Lean file per pair from the emitted
  ``exprA``/``exprB`` and times ``lake env lean -Dprofiler=true``,
  charging every profiler category except import, initialization, and
  parsing, so the tactic tier includes elaboration, compiled search,
  and the decisive kernel replay but not the fixed import cost.

A cactus plot answers "how many instances does each tier solve within a
per-instance time budget": each curve sorts its own per-instance times
ascending; a point (k, t) means the k-th easiest instance took t.
Tactic runs that exceed ``--tactic-timeout`` count as unsolved.

Usage:

    lake exe hexgraphiso_cactus        > sweep.jsonl
    lake exe hexgraphiso_cactus pairs  > pairs.jsonl
    python3 scripts/plots/hexgraphiso-cactus.py \
        --sweep sweep.jsonl --pairs pairs.jsonl

Figures land in ``reports/figures/`` (the repo convention, published
through the manual's ``extraFiles``). The tactic leg re-runs Lean per
pair (minutes); cached results land in
``<out-dir>/hexgraphiso-tactic-times.json`` and are reused unless
``--retime``.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

TACTIC_FILE = """import HexGraphIso
open Hex.GraphIso
def A : Colored {n} 1 := {exprA}
def B : Colored {n} 1 := {exprB}
example : {goal} := by graph_iso (maxNodes := 100000000) (maxCheckerSteps := 1000000000)
"""

_TIME = re.compile(r"^\t(.+?) ([0-9.]+)(ms|s|m)$")
_SCALE = {"ms": 1e-3, "s": 1.0, "m": 60.0}
_EXCLUDED = {"import", "initialization", "parsing"}


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def _tactic_seconds(record: dict, timeout: float) -> float | None:
    """Time one graph_iso proof; None if it timed out or failed."""
    goal = "Isomorphic A B" if record["iso"] else "¬ Isomorphic A B"
    source = TACTIC_FILE.format(n=record["n"], exprA=record["exprA"],
                                exprB=record["exprB"], goal=goal)
    with tempfile.NamedTemporaryFile(
            "w", suffix=".lean", dir=REPO_ROOT, delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "-Dprofiler=true", str(path)],
            cwd=REPO_ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    finally:
        path.unlink()
    if proc.returncode != 0:
        print(f"tactic failed on {record['name']}:\n{proc.stderr[-2000:]}",
              file=sys.stderr)
        return None
    total = 0.0
    in_block = False
    for line in (proc.stdout + proc.stderr).splitlines():
        if line.startswith("cumulative profiling times:"):
            in_block = True
            continue
        if not in_block:
            continue
        match = _TIME.match(line)
        if not match:
            break
        category, value, unit = match.groups()
        if category not in _EXCLUDED:
            total += float(value) * _SCALE[unit]
    return total


def _cactus(ax, series: dict[str, list[float]], total: int) -> None:
    for label, times in series.items():
        solved = sorted(times)
        ax.plot(range(1, len(solved) + 1), solved, marker="o",
                markersize=3, label=f"{label} ({len(solved)}/{total})")
    ax.set_yscale("log")
    ax.set_xlabel("instances solved")
    ax.set_ylabel("per-instance time (s)")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sweep", type=Path, required=True)
    parser.add_argument("--pairs", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path,
                        default=REPO_ROOT / "reports/figures")
    parser.add_argument("--tactic-timeout", type=float, default=120.0)
    parser.add_argument("--retime", action="store_true")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    sweep = _read_jsonl(args.sweep)
    fig, (ax_cactus, ax_family) = plt.subplots(1, 2, figsize=(13, 5))
    _cactus(ax_cactus, {
        "nauty 2.9.3 (C, no proof object)":
            [r["nauty_ns"] / 1e9 for r in sweep],
        "hex canonicalize (fast, conformance-pinned)":
            [r["fast_ns"] / 1e9 for r in sweep],
        "hex Checked.canonicalize (validated certificate)":
            [r["checked_ns"] / 1e9 for r in sweep],
    }, len(sweep))
    ax_cactus.set_title("canonical labelling: cactus over "
                        f"{len(sweep)} family instances")
    families = sorted({r["family"] for r in sweep})
    for family in families:
        rows = sorted((r for r in sweep if r["family"] == family),
                      key=lambda r: r["n"])
        line, = ax_family.plot([r["n"] for r in rows],
                               [r["checked_ns"] / 1e9 for r in rows],
                               marker="o", markersize=3, label=family)
        ax_family.plot([r["n"] for r in rows],
                       [r["fast_ns"] / 1e9 for r in rows],
                       linestyle=":", linewidth=1.4, marker="o",
                       markersize=2, color=line.get_color())
        ax_family.plot([r["n"] for r in rows],
                       [r["nauty_ns"] / 1e9 for r in rows],
                       linestyle="--", linewidth=1, marker="o",
                       markersize=2, color=line.get_color())
    ax_family.set_yscale("log")
    ax_family.set_xlabel("n (vertices)")
    ax_family.set_ylabel("canonicalize time (s)")
    ax_family.set_title(
        "by family: checked (solid), fast (dotted), nauty (dashed)")
    ax_family.grid(True, which="both", alpha=0.3)
    ax_family.legend(fontsize=8)
    fig.text(0.5, 0.005,
             "min of 5 reps after warmup, blackBox-sunk results, "
             "doubled-batch scaling self-check; single machine, "
             "compiled binaries only",
             ha="center", fontsize=7, style="italic")
    canon_png = args.out_dir / "hexgraphiso-canon-cactus.svg"
    fig.tight_layout()
    fig.savefig(canon_png)
    plt.close(fig)

    pairs = _read_jsonl(args.pairs)
    cache_path = args.out_dir / "hexgraphiso-tactic-times.json"
    cache: dict[str, float | None] = {}
    if cache_path.exists() and not args.retime:
        cache = json.loads(cache_path.read_text())
    for record in pairs:
        if record["name"] not in cache:
            print(f"timing graph_iso on {record['name']} ...",
                  file=sys.stderr)
            cache[record["name"]] = _tactic_seconds(
                record, args.tactic_timeout)
            cache_path.write_text(json.dumps(cache, indent=1))

    fig, ax = plt.subplots(figsize=(7.5, 5))
    tactic_times = [cache[r["name"]] for r in pairs
                    if cache.get(r["name"]) is not None]
    _cactus(ax, {
        "nauty 2.9.3 (C, no proof object)":
            [r["nauty_ns"] / 1e9 for r in pairs],
        "hex isIso (fast, conformance-pinned)":
            [r["fast_ns"] / 1e9 for r in pairs],
        "hex Checked.isIso (validated certificate)":
            [r["checked_ns"] / 1e9 for r in pairs],
        "graph_iso tactic (kernel-checked proof)": tactic_times,
    }, len(pairs))
    positives = sum(1 for r in pairs if r["iso"])
    ax.set_title(f"isomorphism proof obligations: {positives} positive, "
                 f"{len(pairs) - positives} negative")
    pairs_png = args.out_dir / "hexgraphiso-pairs-cactus.svg"
    fig.tight_layout()
    fig.savefig(pairs_png)
    plt.close(fig)

    print(canon_png)
    print(pairs_png)
    return 0


if __name__ == "__main__":
    sys.exit(main())
