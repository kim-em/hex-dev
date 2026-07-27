#!/usr/bin/env python3
"""Plot factorization replay, certificate tactics, and Rabin replay shapes.

The upper panel compares total fresh-module wall time for direct kernel
evaluation of ``Hex.ZPoly.factorize``, end-to-end ``factor_poly``, and
end-to-end ``irreducibility``.  The lower panel compares the two kernel Rabin
checkers on identical reified literal factors and certificates.

Input is schema 2 from ``scripts/bench/kernel_factor_sweep.py``.  Output is the
deterministic SVG ``reports/figures/hexbz-kernel-factor-frontier.svg``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hexbz-kernel-frontier"
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import FuncFormatter

ROOT = Path(__file__).resolve().parents[2]
FIGURES = ROOT / "reports" / "figures"

STYLE = {
    "certificate-boundary": ("#111111", "o"),
    "cyclotomic": ("#1f77b4", "o"),
    "cyclotomic-products": ("#17becf", "s"),
    "swinnerton-dyer": ("#d62728", "^"),
    "sd-products": ("#e377c2", "v"),
    "chebyshev": ("#2ca02c", "D"),
    "legendre": ("#9467bd", "P"),
    "laguerre": ("#8c564b", "X"),
    "wilkinson": ("#ff7f0e", "*"),
    "random-products": ("#bcbd22", "h"),
    "hoeij-zimmermann": ("#7f7f7f", "p"),
    "conway": ("#3366aa", ">"),
}
CENSORED = {"timeout", "maxRecDepth", "maxHeartbeats"}
SERIES = {
    "kernel_factor": ("ZPoly.factorize, kernel", "-", True),
    "factor_poly": ("factor_poly, end-to-end", "--", False),
    "irreducibility": ("irreducibility, end-to-end", ":", False),
}


def seconds_formatter(value, _position):
    if value <= 0:
        return "0"
    if value >= 1:
        return f"{value:.0f}s"
    if value >= 1e-3:
        return f"{value * 1e3:.0f}ms"
    return f"{value * 1e6:.0f}us"


def total_seconds(result, series):
    timing = result.get(series, {})
    nanos = timing.get("total_nanos")
    return None if nanos is None else nanos / 1e9


def plot_main(ax, report):
    timeout = report["config"]["timeout_seconds"]
    baselines = report["config"]["import_baseline_nanos"]
    by_family = {}
    for result in report["results"]:
        by_family.setdefault(result["family"], []).append(result)

    for family in sorted(by_family):
        color, marker = STYLE.get(family, ("#333333", "."))
        rows = sorted(by_family[family], key=lambda row: (row["degree"], row["name"]))
        for series, (_label, linestyle, filled) in SERIES.items():
            solved = [
                (row["degree"], total_seconds(row, series))
                for row in rows
                if row.get(series, {}).get("status") == "ok"
                and total_seconds(row, series) is not None
            ]
            if solved:
                ax.plot(
                    [degree for degree, _seconds in solved],
                    [seconds for _degree, seconds in solved],
                    color=color,
                    linestyle=linestyle,
                    marker=marker,
                    markerfacecolor=color,
                    markersize=5,
                    linewidth=1.15,
                )
            censored = [
                row["degree"] for row in rows
                if row.get(series, {}).get("status") in CENSORED
            ]
            if censored:
                ax.plot(
                    [min(censored)], [timeout], marker=marker, color=color,
                    markerfacecolor="none", markeredgewidth=1.5,
                    markersize=8, linestyle="none",
                )
            declines = [
                (row["degree"], total_seconds(row, series))
                for row in rows
                if row.get(series, {}).get("status") == "provider-decline"
                and total_seconds(row, series) is not None
            ]
            if declines:
                ax.scatter(
                    [degree for degree, _seconds in declines],
                    [seconds for _degree, seconds in declines],
                    marker="x", color=color, s=42, linewidths=1.4, zorder=3,
                )

    ax.axhline(timeout, color="#999999", linewidth=0.8, linestyle="--")
    kernel_baseline = baselines.get("kernel_factor")
    certificate_baseline = baselines.get("certificate")
    if kernel_baseline is not None:
        ax.axhline(kernel_baseline / 1e9, color="#666666", linewidth=0.8,
                   linestyle=(0, (1, 2)))
    if certificate_baseline is not None:
        ax.axhline(certificate_baseline / 1e9, color="#666666", linewidth=0.8,
                   linestyle=(0, (5, 2)))
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_xlabel("polynomial degree")
    ax.set_ylabel("total fresh Lake module time")
    ax.set_title("Kernel factorization versus certificate-backed tactics\n"
                 "(unequal fixed import baselines shown in gray)")
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)

    family_handles = [
        Line2D([0], [0], color=STYLE.get(family, ("#333333", "."))[0],
               marker=STYLE.get(family, ("#333333", "."))[1],
               linestyle="none", label=family)
        for family in sorted(by_family)
    ]
    method_handles = [
        Line2D([0], [0], color="#333333", linestyle=linestyle,
               marker="o", markerfacecolor="#333333",
               label=label)
        for label, linestyle, filled in SERIES.values()
    ]
    status_handles = [
        Line2D([0], [0], color="#555555", marker="x", linestyle="none",
               label="provider decline"),
        Line2D([0], [0], color="#555555", marker="o", markerfacecolor="none",
               linestyle="none", label="timeout/resource limit"),
        Line2D([0], [0], color="#666666", linestyle=(0, (1, 2)),
               label="factor import baseline"),
        Line2D([0], [0], color="#666666", linestyle=(0, (5, 2)),
               label="certificate import baseline"),
    ]
    first = ax.legend(handles=method_handles + status_handles, fontsize=7,
                      loc="upper left")
    ax.add_artist(first)
    ax.legend(handles=family_handles, fontsize=7, loc="lower right", ncol=2)


def plot_rabin(ax, report):
    rows = []
    for result in report["results"]:
        for replay in result.get("rabin_replay", []):
            rows.append((result["name"], replay))
    if not rows:
        ax.text(0.5, 0.5, "No multi-prime Rabin replay cases in this record",
                ha="center", va="center", transform=ax.transAxes)
        ax.set_axis_off()
        return

    labels = []
    linear_x, linear_y = [], []
    incremental_x, incremental_y = [], []
    for index, (name, replay) in enumerate(rows):
        labels.append(f"{name}\np={replay['prime']}, d={replay['degree']}")
        linear = replay["linear"]
        incremental = replay["incremental"]
        if linear["status"] == "ok":
            linear_x.append(index - 0.08)
            linear_y.append(linear["total_nanos"] / 1e9)
            ax.vlines(
                index - 0.08,
                linear.get("min_total_nanos", linear["total_nanos"]) / 1e9,
                linear.get("max_total_nanos", linear["total_nanos"]) / 1e9,
                color="#9467bd", linewidth=1.0, zorder=1,
            )
        if incremental["status"] == "ok":
            incremental_x.append(index + 0.08)
            incremental_y.append(incremental["total_nanos"] / 1e9)
            ax.vlines(
                index + 0.08,
                incremental.get("min_total_nanos", incremental["total_nanos"]) / 1e9,
                incremental.get("max_total_nanos", incremental["total_nanos"]) / 1e9,
                color="#2ca02c", linewidth=1.0, zorder=1,
            )
        if linear["status"] == "ok" and incremental["status"] == "ok":
            ax.plot(
                [index - 0.08, index + 0.08],
                [linear["total_nanos"] / 1e9,
                 incremental["total_nanos"] / 1e9],
                color="#bbbbbb", linewidth=0.7, zorder=1,
            )

    ax.scatter(linear_x, linear_y, color="#9467bd", marker="o", s=30,
               label="Linear", zorder=2)
    ax.scatter(incremental_x, incremental_y, color="#2ca02c", marker="s", s=30,
               label="LinearIncremental", zorder=2)
    ax.set_xticks(range(len(labels)), labels, rotation=25, ha="right", fontsize=7)
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_ylabel("total fresh Lake module time")
    ax.set_title("Rabin checker replay on identical literal data (median and range)")
    ax.grid(True, axis="y", which="both", linewidth=0.3, alpha=0.5)
    ax.legend(fontsize=8)


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument(
        "--output", type=Path,
        default=FIGURES / "hexbz-kernel-factor-frontier.svg",
    )
    args = parser.parse_args()

    report = json.loads(args.record.read_text())
    if report.get("schema_version") != 2:
        parser.error("record must use kernel-factor sweep schema_version 2")

    figure, axes = plt.subplots(2, 1, figsize=(9.2, 8.2), height_ratios=[1.25, 1])
    plot_main(axes[0], report)
    plot_rabin(axes[1], report)

    config = report["config"]
    host = report["env"].get("hostname", "?")
    baselines = config["import_baseline_nanos"]

    def baseline_text(name):
        value = baselines.get(name)
        return "n/a" if value is None else f"{value / 1e9:.2f}s"

    figure.text(
        0.5, 0.005,
        f"host {host}; Lake-built fresh modules; timeout {config['timeout_seconds']:.0f}s; "
        f"import baselines factor {baseline_text('kernel_factor')}, "
        f"certificate {baseline_text('certificate')}; matplotlib {matplotlib.__version__}",
        ha="center", fontsize=7, color="#555555",
    )
    figure.tight_layout(rect=(0, 0.025, 1, 1))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    figure.savefig(args.output, format="svg", metadata={"Date": None})
    plt.close(figure)
    svg = args.output.read_text()
    args.output.write_text("\n".join(line.rstrip() for line in svg.splitlines()) + "\n")
    try:
        print(args.output.relative_to(ROOT))
    except ValueError:
        print(args.output)


if __name__ == "__main__":
    main()
