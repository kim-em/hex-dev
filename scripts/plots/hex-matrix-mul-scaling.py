#!/usr/bin/env python3
"""Scaling figure and speedup table for dense square matrix multiplication.

Two series are measured on the same deterministic integer fixtures by the
`hexmatrix_bench` driver (`bench/HexMatrix/Bench.lean`):

* `runSquareMulChecksum` — the naive `O(n^3)` product;
* `runSquareMulStrassenChecksum` — the default-config `mulStrassen`, whose
  declared model is `n^{log2 7}`.

Each series' per-call median wall time is modelled as a power law `t(n) = C·n^p`,
so on a log-log axis it is a straight line of slope `p`. This script re-reads the
committed bench export (the `--export-file` JSON `hexmatrix_bench run/compare`
writes — a single object with a top-level `results` list, each result carrying
`trial_summaries` of `{param, median_per_call_nanos}`), fits `p` for each series
by ordinary least squares on `(log n, log t)` over an explicit asymptotic window,
emits `reports/figures/hex-matrix-mul-scaling.svg`, and prints a speedup table.

The window default is `n >= WINDOW_LO`, chosen past the crossover transient and
spanning the measured rungs (see `SPEC/hex-matrix.md §Benchmarks`). The fitted
Strassen exponent sits **above** `log2 7 ≈ 2.807` on the row-of-rows backing and
at the benched sizes — this is expected and is a diagnostic, not an acceptance
condition. The figure's point is the visibly shallower Strassen slope and the
marked crossover (the cutoff boundary when the fitted-line meet extrapolates
below the measured range).

Run: `python3 scripts/plots/hex-matrix-mul-scaling.py`
(optionally `--data <export.json>`, `--window-lo N`, `--window-hi N`).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-matrix-mul-scaling"
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.ticker import FuncFormatter  # noqa: E402

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

LOG2_7 = math.log2(7.0)

# The committed scaling export. A glob picks the newest matching file so a
# re-measured export drops in without editing this script.
DATA_GLOB = "reports/bench-results/hex-matrix-mul-scaling-*.json"

NAIVE_FN = "runSquareMulChecksum"
STRASSEN_FN = "runSquareMulStrassenChecksum"

# The shipped `strassenDefault.cutoff` (HexMatrix/Strassen.lean). Below it the
# default-config `mulStrassen` IS the naive base kernel (identical work, series
# tied), so the measured crossover of the two series is this boundary: the
# recursion first fires — and, per the committed cutoff sweep, first wins — at
# `n >= cutoff`. Marked on the figure when the fitted-line meet extrapolates
# below the measured range (the fits are windowed to the asymptotic rungs, so
# their intersection point is an extrapolation, not a measurement).
DEFAULT_CUTOFF = 96

# Default asymptotic window: the top rungs where both curves are in their
# asymptotic regime, past the crossover transient near the cutoff. The naive
# crossover with the default-config Strassen sits well below this, so the whole
# window is post-crossover. Widen at your peril: the small-n rungs carry fixed
# per-call and cache-warm-up overhead that bends the fit.
WINDOW_LO = 128
WINDOW_HI = 1024

SERIES_STYLE = {
    NAIVE_FN: {"label": "naive mul", "marker": "o", "color": "#c1443c",
               "linewidth": 2.0, "markersize": 7.0},
    STRASSEN_FN: {"label": "mulStrassen (default cfg)", "marker": "s",
                  "color": "#2f6db3", "linewidth": 2.0, "markersize": 7.0},
}


def seconds_formatter(value: float, _pos: float | None = None) -> str:
    if value <= 0:
        return "0"
    if value >= 1.0:
        return f"{value:.0f} s" if value >= 10 else f"{value:.1f} s"
    if value >= 1e-3:
        return f"{value * 1e3:.0f} ms"
    return f"{value * 1e6:.0f} us"


def default_data_path() -> Path:
    hits = sorted(ROOT.glob(DATA_GLOB))
    if not hits:
        raise SystemExit(
            f"no scaling export found at {DATA_GLOB}; run "
            "`hexmatrix_bench run ... --export-file <path>` and commit it."
        )
    return hits[-1]


def load_series(path: Path, fn_suffix: str) -> dict[int, float]:
    """Map `param -> median seconds per call` for the result whose function name
    ends in `fn_suffix`, reading the `trial_summaries` medians."""
    data = json.loads(path.read_text(encoding="utf-8"))
    for result in data["results"]:
        if not result.get("function", "").endswith(fn_suffix):
            continue
        out: dict[int, float] = {}
        for ts in result.get("trial_summaries", []):
            med = ts.get("median_per_call_nanos")
            if med is not None:
                out[int(ts["param"])] = med / 1e9
        if not out:
            raise SystemExit(f"no timed rungs for {fn_suffix} in {path}")
        return out
    raise SystemExit(f"no result matching {fn_suffix} in {path}")


def provenance(path: Path) -> str:
    env = json.loads(path.read_text(encoding="utf-8")).get("env", {})
    rel = path.relative_to(ROOT)
    return (f"`{rel}` — host `{env.get('hostname')}`, commit "
            f"`{str(env.get('git_commit', '?'))[:8]}`, "
            f"toolchain `{env.get('lean_toolchain', '?')}`")


def fit_power_law(pts: list[tuple[int, float]]) -> tuple[float, float, float]:
    """OLS on (log n, log t). Returns (exponent p, intercept logC, R^2)."""
    lx = [math.log(n) for n, _ in pts]
    ly = [math.log(t) for _, t in pts]
    k = len(pts)
    mx, my = sum(lx) / k, sum(ly) / k
    sxx = sum((v - mx) ** 2 for v in lx)
    sxy = sum((a - mx) * (b - my) for a, b in zip(lx, ly))
    syy = sum((v - my) ** 2 for v in ly)
    p = sxy / sxx
    log_c = my - p * mx
    r2 = (sxy * sxy) / (sxx * syy) if syy > 0 else 1.0
    return p, log_c, r2


def cubic_constant_ns(pts: list[tuple[int, float]]) -> float:
    """Geometric mean of t(n)/n^3 over the window, in nanoseconds."""
    logs = [math.log(t * 1e9) - 3 * math.log(n) for n, t in pts]
    return math.exp(sum(logs) / len(logs))


def window(series: dict[int, float], lo: int, hi: int) -> list[tuple[int, float]]:
    pts = [(n, t) for n, t in sorted(series.items()) if lo <= n <= hi]
    if len(pts) < 2:
        raise SystemExit(f"need >=2 rungs in [{lo}, {hi}], got {[n for n, _ in pts]}")
    return pts


def crossover_n(naive_fit: tuple[float, float], str_fit: tuple[float, float]) -> float | None:
    """Dimension where the two fitted power laws meet: C_n·n^p_n = C_s·n^p_s."""
    p_n, logc_n = naive_fit
    p_s, logc_s = str_fit
    if abs(p_n - p_s) < 1e-9:
        return None
    return math.exp((logc_s - logc_n) / (p_n - p_s))


def report(naive: dict[int, float], strassen: dict[int, float],
           lo: int, hi: int, data_path: Path) -> str:
    n_pts = window(naive, lo, hi)
    s_pts = window(strassen, lo, hi)
    p_n, logc_n, r2_n = fit_power_law(n_pts)
    p_s, logc_s, r2_s = fit_power_law(s_pts)
    c3_n = cubic_constant_ns(n_pts)
    c3_s = cubic_constant_ns(s_pts)
    xover = crossover_n((p_n, logc_n), (p_s, logc_s))

    shared = sorted(set(naive) & set(strassen))
    top = shared[-1] if shared else None

    out = [f"### dense square multiplication, window n∈[{lo}, {hi}]", ""]
    out.append(provenance(data_path))
    out.append("")
    out += [
        "| method | exponent p | R² | C₃ (ns·n³) | per-call @ n=%d |" % (top or hi),
        "|---|---:|---:|---:|---:|",
    ]
    for label, p, r2, c3, series in (
        ("naive mul", p_n, r2_n, c3_n, naive),
        ("mulStrassen (default)", p_s, r2_s, c3_s, strassen),
    ):
        cell = f"{seconds_formatter(series[top])}" if top in series else "—"
        out.append(f"| {label} | {p:.2f} | {r2:.4f} | {c3:.0f} | {cell} |")
    out.append("")
    if top is not None and top in naive and top in strassen:
        sp = naive[top] / strassen[top]
        out.append(
            f"Speedup at the largest benched dimension n={top}: "
            f"naive {seconds_formatter(naive[top])} / Strassen "
            f"{seconds_formatter(strassen[top])} = **{sp:.2f}×**."
        )
    out.append("")
    out.append(
        f"Fitted naive slope {p_n:.2f} (≈ cubic 3.0); fitted Strassen slope "
        f"{p_s:.2f} — shallower, above the diagnostic `log₂ 7 ≈ {LOG2_7:.3f}` as "
        "the SPEC notes for the row-of-rows backing at these sizes."
    )
    if xover is not None:
        out.append(
            f"The fitted lines meet at n ≈ {xover:.0f} — an extrapolation below "
            f"the fit window. The *measured* crossover is the cutoff boundary "
            f"n = {DEFAULT_CUTOFF}: below it the default config runs the naive "
            "base kernel (series tied), and from the first splitting rung the "
            "Strassen series is strictly faster."
        )
    return "\n".join(out)


def plot(naive: dict[int, float], strassen: dict[int, float],
         lo: int, hi: int, output: Path) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))

    for fn, series in ((NAIVE_FN, naive), (STRASSEN_FN, strassen)):
        xs = sorted(series)
        ys = [series[x] for x in xs]
        ax.plot(xs, ys, **SERIES_STYLE[fn])

    # Fit lines over the window, drawn across the full x-range.
    p_n, logc_n, _ = fit_power_law(window(naive, lo, hi))
    p_s, logc_s, _ = fit_power_law(window(strassen, lo, hi))
    all_x = sorted(set(naive) | set(strassen))
    xg = [all_x[0], all_x[-1]]
    ax.plot(xg, [math.exp(logc_n) * x ** p_n for x in xg],
            color=SERIES_STYLE[NAIVE_FN]["color"], linestyle=":", linewidth=1.2,
            label=f"naive fit  p={p_n:.2f}")
    ax.plot(xg, [math.exp(logc_s) * x ** p_s for x in xg],
            color=SERIES_STYLE[STRASSEN_FN]["color"], linestyle=":", linewidth=1.2,
            label=f"Strassen fit  p={p_s:.2f}")

    xover = crossover_n((p_n, logc_n), (p_s, logc_s))
    if xover is not None and all_x[0] <= xover <= all_x[-1]:
        yv = math.exp(logc_n) * xover ** p_n
        ax.axvline(xover, color="0.5", linestyle="--", linewidth=1.0, alpha=0.7)
        ax.annotate(f"crossover ≈ n={xover:.0f}", xy=(xover, yv),
                    xytext=(6, 8), textcoords="offset points",
                    fontsize=8, color="0.35")
    else:
        # The fitted meet extrapolates below the measured range; the honest
        # measured crossover is the cutoff boundary — below it the two series
        # are the same computation.
        yv = math.exp(logc_n) * DEFAULT_CUTOFF ** p_n
        ax.axvline(DEFAULT_CUTOFF, color="0.5", linestyle="--", linewidth=1.0,
                   alpha=0.7)
        ax.annotate(f"crossover = cutoff = {DEFAULT_CUTOFF}\n(identical below)",
                    xy=(DEFAULT_CUTOFF, yv), xytext=(8, -34),
                    textcoords="offset points", fontsize=8, color="0.35")

    ax.set_title("Dense square Int matrix multiplication: naive vs Strassen-Winograd")
    ax.set_xlabel("matrix dimension n")
    ax.set_ylabel("median wall time per call")
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_xticks(all_x)
    ax.get_xaxis().set_major_formatter(FuncFormatter(lambda v, _p: f"{int(v)}"))
    ax.grid(True, which="both", axis="y", alpha=0.25)
    ax.grid(True, which="major", axis="x", alpha=0.15)
    ax.legend(frameon=False, fontsize=8)
    fig.tight_layout()

    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, format="svg", metadata={"Date": None})
    svg = output.read_text(encoding="utf-8")
    output.write_text("\n".join(line.rstrip() for line in svg.splitlines()) + "\n",
                      encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=Path, default=None,
                        help="Override the committed scaling export.")
    parser.add_argument("--window-lo", type=int, default=WINDOW_LO)
    parser.add_argument("--window-hi", type=int, default=WINDOW_HI)
    parser.add_argument("--output", type=Path,
                        default=ROOT / "reports/figures/hex-matrix-mul-scaling.svg")
    args = parser.parse_args()

    data_path = args.data or default_data_path()
    naive = load_series(data_path, NAIVE_FN)
    strassen = load_series(data_path, STRASSEN_FN)

    print(report(naive, strassen, args.window_lo, args.window_hi, data_path))
    plot(naive, strassen, args.window_lo, args.window_hi, args.output)
    print(f"\nwrote {args.output.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
