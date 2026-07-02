#!/usr/bin/env python3
"""Generate the Swinnerton-Dyer tier-crossover figures from committed bench exports.

Three one-parameter families (see `bench/HexBerlekampZassenhaus/Bench.lean`,
"Swinnerton-Dyer tier-crossover ladders"):

* ``sd-ladder``  — `SD_k`, k = 1..5 (irreducible; classical certification)
* ``sd-pair``    — `SD_k(x)·SD_k(x+1)`, k = 1..5 (classical → lattice at k = 5)
* ``sd4-blocks`` — `∏_{i<m} SD_4(x+i)`, m = 1..4 (classical → lattice at m = 3)

Each figure draws log-y median wall time per call against the family
parameter: the hex `factor` curve from the lean-bench export, the verified
Isabelle (AFP Berlekamp_Zassenhaus extraction) rungs from their fixed
registrations, and the informational python-flint curve from the companion
`hex-berlekamp-zassenhaus-sd-flint.py` export. Missing comparator rungs are
annotated rather than silently dropped (the pair family's k = 5 Isabelle rung
exceeded a 120 s cap: the AFP implementation has no lattice tier).

Usage: hex-berlekamp-zassenhaus-sd.py [--sha SHORTSHA] [--out-dir DIR]
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-berlekamp-zassenhaus-sd"
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports/bench-results"
FIGURES = ROOT / "reports/figures"

ISABELLE_RUNG = re.compile(
    r"runIsabelleAdvSwinnertonDyer"
    r"(?:SD(?P<ladder>[0-9]+)|PairK(?P<pair>[0-9]+)|SD4BlocksM(?P<blocks>[0-9]+))"
    r"Checksum$"
)
# Trivial-input (constant polynomial 1) round trip through the persistent
# comparator: the per-request overhead every Isabelle rung pays. Subtracted
# from the Isabelle curves, mirroring the headline report's ratio convention.
ISABELLE_BASELINE = re.compile(r"runIsabelleFactorBaselineChecksum$")

FAMILIES = {
    "sd-ladder": {
        "title": "Swinnerton-Dyer ladder  SD$_k$  (irreducible)",
        "xlabel": "k   (degree $2^k$, $r = 2^{k-1}$ local factors)",
        "hex_export": "sd-ladder",
        "flint_family": "ladder",
        "isabelle_group": "ladder",
        "crossover": None,
        "missing_isabelle": {},
    },
    "sd-pair": {
        "title": "Pair ladder  SD$_k(x)\\,\\cdot\\,$SD$_k(x+1)$",
        "xlabel": "k   (degree $2^{k+1}$, two $2^{k-1}$-blocks)",
        "hex_export": "sd-pair",
        "flint_family": "pair",
        "isabelle_group": "pair",
        "crossover": (5, "classical declines at level boundary;\nCLD lattice tier answers"),
        "missing_isabelle": {5: "> 120 s\n(no lattice tier)"},
    },
    "sd4-blocks": {
        "title": "Block ladder  $\\prod_{i<m}$ SD$_4(x+i)$",
        "xlabel": "m   (degree $16m$, $m$ blocks of eight local factors)",
        "hex_export": "sd4-blocks",
        "flint_family": "blocks",
        "isabelle_group": "blocks",
        "crossover": (3, "classical declines at level boundary;\nCLD lattice tier answers"),
        "missing_isabelle": {},
    },
}


def newest(pattern: str) -> Path:
    """The unique committed export matching the pattern.

    Refuses to guess between sweeps: once exports from more than one commit
    match, an explicit `--sha` is required.
    """
    matches = sorted(RESULTS.glob(pattern))
    if not matches:
        raise SystemExit(f"no bench export matches {pattern} under {RESULTS}")
    if len(matches) > 1:
        names = ", ".join(m.name for m in matches)
        raise SystemExit(
            f"multiple exports match {pattern} ({names}); pass an explicit --sha")
    return matches[0]


def load_hex_curve(path: Path) -> dict[int, float]:
    data = json.loads(path.read_text())
    curve: dict[int, list[float]] = {}
    for result in data["results"]:
        for point in result["points"]:
            if point["status"] == "ok":
                curve.setdefault(point["param"], []).append(point["per_call_nanos"])
    return {p: sorted(v)[len(v) // 2] / 1e9 for p, v in curve.items()}


def load_isabelle_rungs(path: Path) -> dict[str, dict[int, float]]:
    data = json.loads(path.read_text())
    rungs: dict[str, dict[int, float]] = {"ladder": {}, "pair": {}, "blocks": {}}
    baseline_s = 0.0
    for result in data["results"]:
        if ISABELLE_BASELINE.search(result["function"]):
            baseline_s = result["median_nanos"] / 1e9
    for result in data["results"]:
        m = ISABELLE_RUNG.search(result["function"])
        if not m:
            continue
        raw_s = result["median_nanos"] / 1e9
        if raw_s <= baseline_s:
            print(f"warning: {result['function']} is baseline-limited "
                  f"({raw_s * 1e3:.3f} ms <= baseline {baseline_s * 1e3:.3f} ms); "
                  "dropping the rung rather than plotting an artificial point")
            continue
        median_s = raw_s - baseline_s
        if m.group("ladder"):
            rungs["ladder"][int(m.group("ladder"))] = median_s
        elif m.group("pair"):
            rungs["pair"][int(m.group("pair"))] = median_s
        elif m.group("blocks"):
            k = int(m.group("blocks"))
            rungs["blocks"][k] = median_s
    # Duplicated inputs across families: the block rung m = 1 is SD_4 itself,
    # and the block rung m = 2 is the pair rung k = 4 (SD_4(x)·SD_4(x+1)).
    # Reuse those measurements on the blocks curve.
    if 4 in rungs["ladder"] and 1 not in rungs["blocks"]:
        rungs["blocks"][1] = rungs["ladder"][4]
    if 4 in rungs["pair"] and 2 not in rungs["blocks"]:
        rungs["blocks"][2] = rungs["pair"][4]
    return rungs


def load_flint(path: Path) -> dict[str, dict[int, float]]:
    data = json.loads(path.read_text())
    out: dict[str, dict[int, float]] = {}
    for row in data["results"]:
        out.setdefault(row["family"], {})[row["param"]] = row["median_seconds_per_call"]
    return out


def draw(family: str, spec: dict, hex_curve: dict[int, float],
         isabelle: dict[int, float], flint: dict[int, float],
         missing: dict[int, str], out: Path) -> None:
    fig, ax = plt.subplots(figsize=(6.4, 4.2))
    for label, curve, style in [
        ("hex `factor` (hybrid)", hex_curve, dict(marker="o", color="#1f77b4")),
        ("Isabelle (verified AFP, overhead-subtracted)", isabelle,
         dict(marker="s", color="#d62728")),
        ("FLINT (informational)", flint, dict(marker="^", color="#7f7f7f", linestyle="--")),
    ]:
        if curve:
            xs = sorted(curve)
            ax.plot(xs, [curve[x] for x in xs], label=label, **style)
    for param, note in missing.items():
        # An off-scale comparator rung: mark it with a rising dotted red tail
        # from the last measured rung instead of a point.
        last = max(isabelle)
        ax.plot([last, param], [isabelle[last], ax.get_ylim()[1] * 2],
                color="#d62728", linestyle=":", lw=1.0, clip_on=True)
        ax.text(param - 0.08, ax.get_ylim()[1] * 0.30, f"Isabelle {note}",
                ha="right", va="top", fontsize=8, color="#d62728")
    if spec["crossover"]:
        param, note = spec["crossover"]
        ax.axvline(param - 0.5, color="#2ca02c", linestyle=":", lw=1.2)
        ax.text(param - 0.58, min(hex_curve.values()) * 1.5, note,
                fontsize=8, color="#2ca02c", va="bottom", ha="right")
    ax.set_yscale("log")
    ax.set_xticks(sorted(hex_curve))
    ax.set_xlabel(spec["xlabel"])
    ax.set_ylabel("median wall time per call (s)")
    ax.set_title(spec["title"], fontsize=11)
    ax.grid(True, which="both", alpha=0.25)
    ax.legend(fontsize=8, loc="upper left")
    fig.tight_layout()
    fig.savefig(out, metadata={"Date": None})
    plt.close(fig)
    print(f"wrote {out}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sha", default="*", help="short SHA of the exports to plot")
    parser.add_argument("--out-dir", type=Path, default=FIGURES)
    args = parser.parse_args()

    isabelle = load_isabelle_rungs(
        newest(f"hex-berlekamp-zassenhaus-{args.sha}-sd-isabelle.json"))
    flint = load_flint(newest(f"hex-berlekamp-zassenhaus-{args.sha}-sd-flint.json"))
    args.out_dir.mkdir(parents=True, exist_ok=True)
    for family, spec in FAMILIES.items():
        hex_curve = load_hex_curve(
            newest(f"hex-berlekamp-zassenhaus-{args.sha}-{spec['hex_export']}.json"))
        draw(family, spec, hex_curve,
             isabelle.get(spec["isabelle_group"], {}),
             flint.get(spec["flint_family"], {}),
             spec["missing_isabelle"],
             args.out_dir / f"hex-berlekamp-zassenhaus-{family}.svg")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
