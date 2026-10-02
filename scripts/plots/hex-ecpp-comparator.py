#!/usr/bin/env python3
"""Plot retained matched ECPP verification observations; collect no new timings."""
import argparse
import json
from pathlib import Path
import statistics

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", required=True, choices=["supplied-certificates"])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    compiled = json.loads((ROOT / "reports/ecpp/compiled.json").read_text())["results"]
    pari = json.loads((ROOT / "reports/ecpp/pari-verify.json").read_text())["rows"]
    bits = [65, 256, 512]
    hex_ms = [next(r["median_nanos"] / 1e6 for r in compiled
                   if r["function"] == f"runCheck{n}") for n in bits]
    pari_ms = [statistics.median(r["elapsed_ms"] / r["repetitions"] for r in pari
                                if r["case"] == f"pari{n}") for n in bits]
    plt.rcParams["svg.hashsalt"] = "hex-ecpp"
    fig, ax = plt.subplots(figsize=(6.4, 4))
    ax.plot(bits, hex_ms, "o-", label="Hex check (explicit terminal certificate)")
    ax.plot(bits, pari_ms, "o-", label="PARI primecertisvalid (integer terminal)")
    ax.set(xlabel="Accepted subject bits", ylabel="Median per verification (ms)",
           yscale="log", title="Retained verification context: Lean 4.34.1 / PARI 2.17.3")
    ax.grid(True, alpha=.25)
    ax.legend(fontsize=8)
    fig.tight_layout()
    output = args.output or ROOT / "reports/figures/hex-ecpp-comparator-supplied-certificates.svg"
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, metadata={"Date": None, "Description":
                "reports/ecpp/{compiled,pari-verify}.json; source de25e7b; shared host CPU 13"})


if __name__ == "__main__":
    main()
