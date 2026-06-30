#!/usr/bin/env python3
"""Fit the asymptotic scaling of the HexLLL comparator runtimes.

Each comparator's median wall time is modelled as a power law in the
dimension `n`,

    t(n)  =  C * n**p ,

so on a log-log axis the curve is a straight line of slope `p`. This script
re-reads the same committed bench exports the comparator plot uses (so the
numbers track the figure), fits `p` over an asymptotic window of rungs by
ordinary least squares on `(log n, log t)`, and reports both the free-fit
exponent and a cubic-pinned leading constant `C3` that makes the methods'
constant factors directly comparable.

`C3` is the geometric mean of `t(n) / n**3` over the window, expressed in
nanoseconds; under the empirical `p ~ 3` it is the per-`n**3` cost, and the
ratio of two methods' `C3` is their constant-factor gap. The `x fpLLL` column
normalises `C3` to the fastest method.

Run `--family random-bounded` (default) or `--family harsh-cubic`, or `--all`.
The data sources, function-name regexes, and family definitions are imported
from `hex-lll-comparator.py`; this script only fits and tabulates.
"""

from __future__ import annotations

import argparse
import importlib.util
import math
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

# Import the sibling comparator module by path (its filename has hyphens, so a
# normal `import` will not work). Reusing it keeps one source of truth for the
# committed data files and the bench function-name regexes.
_spec = importlib.util.spec_from_file_location(
    "hex_lll_comparator", HERE / "hex-lll-comparator.py"
)
cmp = importlib.util.module_from_spec(_spec)
# Register before exec so the module's @dataclass can resolve its own
# __module__ (required on Python 3.14+).
sys.modules["hex_lll_comparator"] = cmp
_spec.loader.exec_module(cmp)

# Default asymptotic window per family: the top rungs where the curves are
# straight on a log-log axis. Widen at your peril -- the small-n rungs carry
# fixed per-call overhead (subprocess fork, GHC start-up) that bends the fit.
DEFAULT_WINDOW = {
    "random-bounded": (120, 180),
    "harsh-cubic": (40, 55),
}


def family_series(family: str) -> list[cmp.Series]:
    """Reconstruct the plotted series for a family, in slowest-to-fastest order."""
    config = cmp.FAMILIES[family]
    cons = cmp.load_results(config.consolidated_path)
    out = [
        cmp.collect_series(cons, config.isabelle_pattern, "Isabelle native"),
        cmp.collect_series(cons, config.lean_pattern, "Lean native"),
    ]
    if config.include_certified:
        ic = cmp.load_results(config.isabelle_certified_path)
        c = cmp.load_results(config.certified_path)
        out.append(
            cmp.collect_series(ic, config.isabelle_certified_pattern,
                               "Isabelle certified")
        )
        out.append(
            cmp.collect_series(cons, config.lean_steered_pattern, "Lean steered")
        )
        out.append(cmp.collect_series(c, config.certified_pattern, "Lean certified"))
    else:
        out.append(
            cmp.collect_series(cons, config.lean_steered_pattern, "Lean steered")
        )
    out.append(cmp.collect_series(cons, config.fpll_pattern, "fpLLL via fplll-ffi"))
    return out


def window_points(series: cmp.Series, lo: int, hi: int) -> tuple[list[int], list[float]]:
    pts = [(n, y) for n, y in zip(series.xs, series.ys) if lo <= n <= hi]
    if len(pts) < 2:
        raise ValueError(
            f"{series.label}: need >=2 rungs in [{lo}, {hi}], got {[n for n, _ in pts]}"
        )
    return [n for n, _ in pts], [y for _, y in pts]


def fit_power_law(xs: list[int], ys_ms: list[float]) -> tuple[float, float, float]:
    """OLS on (log n, log t). Returns (exponent p, intercept logC, R^2)."""
    lx = [math.log(n) for n in xs]
    ly = [math.log(y) for y in ys_ms]
    k = len(xs)
    mx = sum(lx) / k
    my = sum(ly) / k
    sxx = sum((v - mx) ** 2 for v in lx)
    sxy = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    syy = sum((v - my) ** 2 for v in ly)
    p = sxy / sxx
    log_c = my - p * mx
    r2 = (sxy * sxy) / (sxx * syy) if syy > 0 else 1.0
    return p, log_c, r2


def cubic_constant_ns(xs: list[int], ys_ms: list[float]) -> float:
    """Geometric mean of t(n)/n**3 over the window, in nanoseconds."""
    logs = [math.log(y * 1_000_000.0) - 3 * math.log(n) for n, y in zip(xs, ys_ms)]
    return math.exp(sum(logs) / len(logs))


def provenance(family: str) -> list[str]:
    config = cmp.FAMILIES[family]
    paths = {config.consolidated_path}
    if config.include_certified:
        paths.add(config.certified_path)
        paths.add(config.isabelle_certified_path)
    lines = []
    for path in sorted(paths):
        import json

        env = json.loads(path.read_text())["env"]
        rel = path.relative_to(ROOT)
        lines.append(
            f"- `{rel}` — host `{env.get('hostname')}`, commit "
            f"`{env.get('git_commit', '?')[:8]}`"
        )
    return lines


# Exponent spread (max p - min p) below this counts as "a shared exponent":
# the curves are parallel and a single pinned constant describes the gaps.
# Above it the curves fan out and only the observed ratio at a fixed rung is
# meaningful.
SHARED_EXPONENT_SPREAD = 0.5


def report(family: str, lo: int, hi: int) -> str:
    series = family_series(family)
    rows = []
    for s in series:
        xs, ys = window_points(s, lo, hi)
        p, _, r2 = fit_power_law(xs, ys)
        rows.append((s.label, p, r2, cubic_constant_ns(xs, ys), dict(zip(xs, ys))))
    spread = max(p for _, p, *_ in rows) - min(p for _, p, *_ in rows)
    shared = spread <= SHARED_EXPONENT_SPREAD

    out = [f"### {family}, rungs {lo}–{hi}", ""]
    out += provenance(family)
    out.append("")
    if shared:
        fastest = min(c3 for *_, c3, _ in rows)
        out += [
            "| method | exponent p | R² | C₃ (ns·n³) | × fpLLL |",
            "|---|---:|---:|---:|---:|",
        ]
        for label, p, r2, c3, _ in rows:
            out.append(f"| {label} | {p:.2f} | {r2:.4f} | {c3:.0f} | {c3 / fastest:.1f}× |")
        out += [
            "",
            f"Exponents agree to within {spread:.2f}, so the methods share one "
            "complexity and differ only by a constant factor. `t(n) ≈ C₃·n³` "
            "nanoseconds; `× fpLLL` is the constant-factor gap to the fastest method.",
        ]
    else:
        fastest_at_hi = min(ys[hi] for *_, ys in rows)
        out += [
            "| method | exponent p | R² | median @ n=%d | × fastest @ n=%d |" % (hi, hi),
            "|---|---:|---:|---:|---:|",
        ]
        for label, p, r2, _, ys in rows:
            out.append(
                f"| {label} | {p:.2f} | {r2:.4f} | {ys[hi]:.1f} ms "
                f"| {ys[hi] / fastest_at_hi:.1f}× |"
            )
        out += [
            "",
            f"Exponents span {spread:.2f} (no shared complexity): the curves fan "
            "out, so a single constant does not describe the gaps and the ratio is "
            "the observed one at `n=%d`, growing with `n`." % hi,
        ]
    return "\n".join(out)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=sorted(cmp.FAMILIES), default="random-bounded")
    parser.add_argument("--all", action="store_true", help="Report every family.")
    parser.add_argument("--window-lo", type=int, default=None)
    parser.add_argument("--window-hi", type=int, default=None)
    args = parser.parse_args()

    families = sorted(cmp.FAMILIES) if args.all else [args.family]
    blocks = []
    for fam in families:
        lo = args.window_lo or DEFAULT_WINDOW[fam][0]
        hi = args.window_hi or DEFAULT_WINDOW[fam][1]
        blocks.append(report(fam, lo, hi))
    print("\n\n".join(blocks))


if __name__ == "__main__":
    main()
