#!/usr/bin/env python3
"""Kernel cost of the `graph_iso` tactic per certificate record.

Local tooling, not merge CI. The cactus sweep (`scripts/plots/
hexgraphiso-cactus.py`) reports one wallclock number per pair; this
harness reports where a negative pair's time goes and what the kernel
pays per certificate record, so a change to the replay can be judged
by the same measurement every time.

For every selected pair of the `decision-pairs` corpus (the
``hexgraphiso-pairs-*.jsonl`` record the sweep emits) it writes the
same one-proof Lean file the cactus script builds, with
``set_option trace.graph_iso true`` so the tactic reports the route it
closed through and the certificate record counts, runs
``lake lean <file> -- -Dprofiler=true`` on it (``lake lean`` loads the
library's precompiled modules, as a downstream ``lake build`` does), and splits the profiler's
cumulative categories into type checking (the kernel), interpretation
(the compiled search running in the interpreter), elaboration, and the
rest, all excluding import, initialization and parsing. For the
certificate route it divides the type-checking time by the record
count (both sides summed) and fits ``ms/record = c * n^e`` over the
pairs that closed through that route, so the per-record exponent
before and after a change is one number.

``--floor`` additionally times the shared floor of every negative
route: the kernel evaluation of each graph's adjacency into its packed
rows (the tie ``Kernel.packRows n G.graph.adjMatrix.data.toList = N`` the
tactic emits), as one ``of_decide_eq_true`` obligation per side.

Usage:

    python3 scripts/bench/graphiso_kernel_cost.py [--pairs FILE]
        [--names neg-c6-vs-2c3 ...] [--negatives] [--max-n N]
        [--timeout S] [--floor] [--label L] [--out FILE]

``--pairs`` defaults to the newest committed pairs record under
``reports/bench-results/``. The output lands under
``reports/bench-results/hexgraphiso-kernel-<fingerprint>-<host>.json``
unless ``--out`` says otherwise; the fingerprint is the cactus sweep's
(``sweep_freshness.py``'s content fingerprint of the graph-iso source),
so a record is attributable to the source it measured.
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import socket
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
RESULTS = REPO_ROOT / "reports" / "bench-results"

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sweep_freshness as freshness  # noqa: E402

# The measured source is the cactus sweep's family, so a kernel record
# and a sweep record at the same fingerprint describe the same code.
RELEVANT = list(freshness.GRAPHISO.include)

TACTIC_FILE = """import HexGraphIso
set_option trace.graph_iso true
open Hex Hex.GraphIso
def A : Colored {n} 1 := {exprA}
def B : Colored {n} 1 := {exprB}
example : {goal} := by graph_iso (maxSearchNodes := 100000000) (maxKernelSteps := 1000000000)
"""

EVAL_FILE = """import HexGraphIso
open Hex Hex.GraphIso
def A : Colored {n} 1 := {exprA}
def B : Colored {n} 1 := {exprB}
#eval IO.println (toString (Kernel.packRows {n} A.graph.adjMatrix.data.toList))
#eval IO.println (toString (Kernel.packRows {n} B.graph.adjMatrix.data.toList))
"""

FLOOR_FILE = """import HexGraphIso
open Hex Hex.GraphIso
open Lean Meta Elab Tactic in
elab "kdecide" : tactic => do
  let g ← getMainGoal
  let p ← g.getType
  let inst ← synthInstance (← mkAppM ``Decidable #[p])
  let decideApp := mkApp2 (mkConst ``Decidable.decide) p inst
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let eqType ← mkAppM ``Eq #[decideApp, mkConst ``Bool.true]
  let h ← mkExpectedTypeHint refl eqType
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) p inst h)
def A : Colored {n} 1 := {exprA}
def B : Colored {n} 1 := {exprB}
example : Kernel.packRows {n} A.graph.adjMatrix.data.toList = {litA} := by kdecide
example : Kernel.packRows {n} B.graph.adjMatrix.data.toList = {litB} := by kdecide
"""

_TIME = re.compile(r"^\t(.+?) ([0-9.]+)(ms|s|m)$")
_SCALE = {"ms": 1e-3, "s": 1.0, "m": 60.0}
_EXCLUDED = {"import", "initialization", "parsing"}
_ROUTE = re.compile(r"\[graph_iso\] (route=\S+.*)$")


def _read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines()
            if line.strip()]


def _newest_pairs() -> Path:
    """The pairs record of the most recent sweep, by the sweep's own
    recorded date (the `.meta.json` beside its cactus data)."""
    def date(pairs: Path) -> str:
        meta = pairs.with_name(
            pairs.name.replace("hexgraphiso-pairs-", "hexgraphiso-cactus-")
            .replace(".jsonl", ".meta.json"))
        if not meta.exists():
            return ""
        return json.loads(meta.read_text()).get("date", "")
    candidates = sorted(RESULTS.glob("hexgraphiso-pairs-*.jsonl"), key=date)
    if not candidates:
        sys.exit("no hexgraphiso-pairs-*.jsonl under reports/bench-results")
    return candidates[-1]


def _fingerprint() -> str:
    return freshness.fingerprint(freshness.index_listing(freshness.GRAPHISO))


def _run_lean(source: str, timeout: float) -> tuple[str, float, bool, int]:
    """Run one Lean file; return (output, wallclock, timed_out, rc)."""
    with tempfile.NamedTemporaryFile(
            "w", suffix=".lean", dir=REPO_ROOT, delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    start = time.monotonic()
    try:
        # `lake lean` (not `lake env lean`) loads the precompiled
        # `HexGraphIso` shared libraries, as a downstream `lake build`
        # does, so the compiled search runs compiled here too.
        proc = subprocess.run(
            ["lake", "lean", str(path), "--", "-Dprofiler=true"],
            cwd=REPO_ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        out = (exc.stdout or b"").decode(errors="replace") if isinstance(
            exc.stdout, bytes) else (exc.stdout or "")
        return out, time.monotonic() - start, True, -1
    finally:
        path.unlink()
    return (proc.stdout + proc.stderr, time.monotonic() - start, False,
            proc.returncode)


def _profile(output: str) -> dict[str, float]:
    times: dict[str, float] = {}
    in_block = False
    for line in output.splitlines():
        if line.startswith("cumulative profiling times:"):
            in_block = True
            continue
        if not in_block:
            continue
        match = _TIME.match(line)
        if not match:
            break
        category, value, unit = match.groups()
        times[category] = float(value) * _SCALE[unit]
    return times


def _route(output: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in output.splitlines():
        match = _ROUTE.search(line)
        if match:
            fields = dict(kv.split("=", 1) for kv in match.group(1).split())
    return fields


def _measure(record: dict, timeout: float) -> dict:
    goal = "Isomorphic A B" if record["iso"] else "¬ Isomorphic A B"
    source = TACTIC_FILE.format(n=record["n"], exprA=record["exprA"],
                                exprB=record["exprB"], goal=goal)
    output, wall, timed_out, rc = _run_lean(source, timeout)
    result: dict = {"name": record["name"], "n": record["n"],
                    "iso": record["iso"], "family": record.get("family"),
                    "wall_s": round(wall, 3), "timeout": timed_out,
                    "ok": (not timed_out) and rc == 0,
                    "load_1m": round(os.getloadavg()[0], 2)}
    if timed_out:
        return result
    if rc != 0:
        result["stderr"] = output[-2000:]
        return result
    prof = _profile(output)
    result["typecheck_s"] = prof.get("type checking", 0.0)
    result["interp_s"] = prof.get("interpretation", 0.0)
    result["elab_s"] = prof.get("elaboration", 0.0)
    result["total_s"] = sum(v for k, v in prof.items() if k not in _EXCLUDED)
    result["other_s"] = (result["total_s"] - result["typecheck_s"]
                         - result["interp_s"] - result["elab_s"])
    route = _route(output)
    result["route"] = route.get("route")
    for key in ("records", "recordsG", "recordsH", "autom", "steps",
                "nodes"):
        if key in route:
            result[key] = int(route[key])
    if result.get("records"):
        result["ms_per_record"] = 1e3 * result["typecheck_s"] / result["records"]
        # the tactic's own charge: one unit per record, one more per
        # automorphism record (generator validation), two fixed units
        units = result["records"] + result.get("autom", 0) + 2
        result["ms_per_unit"] = 1e3 * result["typecheck_s"] / units
    return result


def _floor(record: dict, timeout: float) -> dict | None:
    source = EVAL_FILE.format(n=record["n"], exprA=record["exprA"],
                              exprB=record["exprB"])
    output, _, timed_out, rc = _run_lean(source, timeout)
    if timed_out or rc != 0:
        return None
    lits = [line.strip() for line in output.splitlines()
            if line.strip().isdigit()]
    if len(lits) < 2:
        return None
    source = FLOOR_FILE.format(n=record["n"], exprA=record["exprA"],
                               exprB=record["exprB"], litA=lits[0],
                               litB=lits[1])
    output, wall, timed_out, rc = _run_lean(source, timeout)
    if timed_out or rc != 0:
        return None
    prof = _profile(output)
    return {"typecheck_s": prof.get("type checking", 0.0),
            "wall_s": round(wall, 3)}


def _fit(points: list[tuple[float, float]]) -> tuple[float, float] | None:
    """Least squares of log y on log x: returns (c, e) with y = c * x^e."""
    if len(points) < 2:
        return None
    xs = [math.log(x) for x, _ in points]
    ys = [math.log(y) for _, y in points]
    mx = sum(xs) / len(xs)
    my = sum(ys) / len(ys)
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return None
    e = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    return math.exp(my - e * mx), e


def _fmt(value, width: int = 8, digits: int = 3) -> str:
    if value is None:
        return "-".rjust(width)
    if isinstance(value, float):
        return f"{value:.{digits}f}".rjust(width)
    return str(value).rjust(width)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--pairs", type=Path)
    parser.add_argument("--names", nargs="*")
    parser.add_argument("--negatives", action="store_true",
                        help="only the negative pairs")
    parser.add_argument("--max-n", type=int)
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--floor", action="store_true")
    parser.add_argument("--label", default="")
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    pairs_path = args.pairs or _newest_pairs()
    pairs = _read_jsonl(pairs_path)
    if args.names:
        wanted = set(args.names)
        pairs = [p for p in pairs if p["name"] in wanted]
    if args.negatives:
        pairs = [p for p in pairs if not p["iso"]]
    if args.max_n is not None:
        pairs = [p for p in pairs if p["n"] <= args.max_n]
    if not pairs:
        sys.exit("no pairs selected")

    fingerprint = _fingerprint()
    dirty = subprocess.run(["git", "status", "--porcelain", "--", *RELEVANT],
                           cwd=REPO_ROOT, capture_output=True, text=True).stdout
    if dirty.strip():
        print("warning: uncommitted changes under the measured paths; the "
              "fingerprint names the index, not what is measured:\n" + dirty,
              file=sys.stderr)
    host = socket.gethostname().split(".")[0]
    load_at_start = round(os.getloadavg()[0], 2)
    results = []
    for record in pairs:
        print(f"measuring {record['name']} (n={record['n']}) ...",
              file=sys.stderr, flush=True)
        result = _measure(record, args.timeout)
        if args.floor:
            result["floor"] = _floor(record, args.timeout)
        results.append(result)
        print(_row(result), flush=True)

    fit_points = [(r["n"], r["ms_per_record"]) for r in results
                  if r.get("route") == "certs" and r.get("ms_per_record")]
    fit = _fit(fit_points)
    summary = {
        "fingerprint": fingerprint,
        "host": host,
        "date": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "describe": subprocess.run(
            ["git", "rev-parse", "--short=12", "HEAD"], cwd=REPO_ROOT,
            capture_output=True, text=True).stdout.strip(),
        "label": args.label,
        "pairs": str(pairs_path.relative_to(REPO_ROOT))
        if pairs_path.is_relative_to(REPO_ROOT) else str(pairs_path),
        "timeout_s": args.timeout,
        "load_1m_at_start": load_at_start,
        "dirty": bool(dirty.strip()),
        "fit_ms_per_record": None if fit is None else
        {"c": fit[0], "exponent": fit[1], "points": len(fit_points)},
        "results": results,
    }
    print()
    print(_header())
    for result in results:
        print(_row(result))
    if fit is not None:
        print(f"\ncertificate route: ms/record ~ {fit[0]:.4f} * n^{fit[1]:.2f} "
              f"over {len(fit_points)} pairs")
    out = args.out or RESULTS / f"hexgraphiso-kernel-{fingerprint}-{host}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(summary, indent=1) + "\n")
    print(f"\nwrote {out}")
    return 0


def _header() -> str:
    return (f"{'pair':32s} {'n':>4s} {'route':>9s} {'records':>8s} "
            f"{'kernel_s':>9s} {'interp_s':>9s} {'elab_s':>8s} {'other_s':>8s} "
            f"{'ms/rec':>8s} {'floor_s':>8s}")


def _row(result: dict) -> str:
    if result.get("timeout"):
        status = f"timeout after {result['wall_s']} s"
        return f"{result['name']:32s} {result['n']:>4d} {status}"
    if not result.get("ok"):
        return f"{result['name']:32s} {result['n']:>4d} FAILED"
    floor = result.get("floor")
    return (f"{result['name']:32s} {result['n']:>4d} "
            f"{_fmt(result.get('route'), 9)} {_fmt(result.get('records'), 8)} "
            f"{_fmt(result.get('typecheck_s'), 9)} "
            f"{_fmt(result.get('interp_s'), 9)} "
            f"{_fmt(result.get('elab_s'), 8)} {_fmt(result.get('other_s'), 8)} "
            f"{_fmt(result.get('ms_per_record'), 8, 2)} "
            f"{_fmt(None if floor is None else floor['typecheck_s'], 8)}")


if __name__ == "__main__":
    sys.exit(main())
