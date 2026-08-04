#!/usr/bin/env python3
"""Model the combined cactus with the quadratic-norm certificate (issue #9133).

The certificate is not on the production path, so its effect on the cactus is a
model, not a measurement. This script *is* the model: it reads pinned records,
states its replacement rule in code, and prints the table
``reports/hexbz-quadratic-norm-certificate.md`` quotes, so the report's numbers
cannot drift from their inputs.

Two placements, differing only in which measured phases a certified row still
pays.

``--placement post-prime`` -- the conservative one. The row runs normalization
and the bounded good-prime walk exactly as today, and the certificate then
replaces the Hensel lift, recombination, proposal replay, and the CLD lattice.
The retained phases are measured per row by ``--entry factorPhaseProfile``; a
row the sweep does not solve is left at its current status, since
``factorPhaseProfile`` runs the whole cascade and would not return on it, so
the model never credits an improvement it has not priced. Note
what this placement does *not* say: it is not gated on the existing
262,144-node recombination budget, which ``sd5``'s 32,768-node walk sits under
and would never trip. It is "attempt the certificate once the modular
factorization is in hand", and the price of attempting it on a row that
declines is the miss overhead the probe records.

``--placement post-normalization`` -- the permissive one. A certified row pays
normalization and the certificate only, so rows the cascade cannot finish
become solved. The cost is that every power-of-two-degree row pays the recovery
attempt whether or not it certifies.

``--only`` restricts the replacement to named rows, which answers the question
"how much of this is the `sd5` family alone?" without re-deriving the table by
hand.

Run::

    lake build hexbz_factor_service
    taskset -c 0 python3 scripts/bench/quadratic_norm_cactus_model.py \\
        --output reports/bench-results/hexbz-quadratic-norm-cactus-model.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import socket
import statistics
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
RESULTS = ROOT / "reports" / "bench-results"
SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"
CERTIFICATE = RESULTS / "hexbz-quadratic-norm-certificate-chungus2.json"

# Phases a certified row still runs, per placement. `factorPhaseProfile` reports
# these by name, and anything not listed is what the certificate replaces.
RETAINED = {
    "post-prime": ("normalization", "primeWalk"),
    "post-normalization": ("normalization",),
}


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout.strip()


def source_dirty() -> bool:
    """Are any tracked files outside `reports/bench-results` modified?

    That directory is excluded on purpose: regenerating a set of records in
    sequence would otherwise have each one report the others as dirt, which
    says nothing about whether the measured source moved. `service_sha256`
    pins the measured binary exactly in any case.
    """
    return bool(git("status", "--porcelain", "--untracked-files=no", "--",
                    ".", ":(exclude)reports/bench-results"))


def load_corpus() -> dict:
    rows = {}
    for line in CORPUS.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            rows[row["name"]] = row
    return rows


def newest(system: str, corpus_sha: str) -> Path:
    candidates = []
    for path in RESULTS.glob("hexbz-factor-sweep-*.json"):
        record = json.loads(path.read_text())
        if record.get("config", {}).get("corpus_sha256") != corpus_sha:
            continue
        if system not in record.get("config", {}).get("systems", []):
            continue
        candidates.append(
            (record.get("env", {}).get("timestamp_unix_ms", 0), path))
    if not candidates:
        raise SystemExit(f"no sweep for {system} matches the current corpus")
    return max(candidates)[1]


def solved_times(path: Path, system: str, names: set) -> dict:
    return {row["name"]: row["median_nanos"] / 1e9
            for row in json.loads(path.read_text())["results"]
            if row["system"] == system and row["name"] in names
            and row["status"] == "ok" and row["median_nanos"] is not None}


def retained_nanos(coeffs: list[int], phases: tuple, repeats: int) -> "int | None":
    """Measured cost of the phases a certified row still pays, or None when the
    production cascade does not finish and the profile cannot be taken.

    The first call in a fresh process is discarded. It is not a warm
    measurement -- on `sd5` the cold prime walk reads about twice the warm one,
    which is enough to move the modelled worst ratio by 0.08x -- and every
    number this model is compared against is warm."""
    payload = "".join(json.dumps({"coeffs": coeffs}) + "\n"
                      for _ in range(repeats + 1))
    completed = subprocess.run(
        [str(SERVICE), "--entry", "factorPhaseProfile"], input=payload,
        text=True, capture_output=True, check=True)
    observed = []
    for line in completed.stdout.splitlines():
        if not line.strip():
            continue
        result = json.loads(line).get("result") or {}
        got = result.get("phases") or {}
        if not all(phase in got for phase in phases):
            return None
        observed.append(sum(got[phase]["nanos"] for phase in phases))
    warm = observed[1:]
    return int(statistics.median(warm)) if warm else None


def cumulative(times: dict) -> list:
    total, out = 0.0, []
    for value in sorted(times.values()):
        total += value
        out.append(total)
    return out


def fmt(seconds) -> str:
    if seconds is None:
        return "--"
    return f"{seconds * 1e3:.3f} ms" if seconds < 1 else f"{seconds:.3f} s"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--placement", choices=sorted(RETAINED),
                        default="post-prime")
    parser.add_argument("--only", help="comma-separated rows to replace")
    parser.add_argument("--lo", type=int, default=125)
    parser.add_argument("--hi", type=int, default=140)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--output")
    args = parser.parse_args(argv[1:])

    if not SERVICE.exists():
        raise SystemExit(f"missing {SERVICE}; run `lake build hexbz_factor_service`")
    corpus = load_corpus()
    combined = {name for name, row in corpus.items() if row.get("combined")}
    corpus_sha = hashlib.sha256(CORPUS.read_bytes()).hexdigest()

    hex_sweep = newest("hex-factor", corpus_sha)
    isabelle_sweep = newest("isabelle-bz", corpus_sha)
    now = solved_times(hex_sweep, "hex-factor", combined)
    isabelle = solved_times(isabelle_sweep, "isabelle-bz", combined)

    certificate = json.loads(CERTIFICATE.read_text())
    certified = {row["name"]: row["certificate_nanos"] for row in certificate["hits"]}
    wanted = set(args.only.split(",")) if args.only else None

    modelled, replacements = dict(now), []
    phases = RETAINED[args.placement]
    for name, cert_nanos in sorted(certified.items()):
        if name not in combined or (wanted is not None and name not in wanted):
            continue
        # Only profile a row the sweep solves: `factorPhaseProfile` runs the
        # whole cascade, so on a row that times out it would never return.
        retained = (retained_nanos(corpus[name]["coeffs"], phases, args.repeats)
                    if name in now else None)
        if retained is None:
            # No profile: the cascade does not reach the end, so this placement
            # cannot be priced for this row. Leave it exactly as measured.
            replacements.append({"name": name, "priced": False,
                                 "now_seconds": now.get(name)})
            continue
        after = (retained + cert_nanos) / 1e9
        replacements.append({
            "name": name, "priced": True, "now_seconds": now.get(name),
            "retained_nanos": retained, "certificate_nanos": cert_nanos,
            "modelled_seconds": after,
        })
        modelled[name] = after

    base, model, other = cumulative(now), cumulative(modelled), cumulative(isabelle)
    ranks = []
    worst_now = worst_model = 0.0
    for rank in range(args.lo, args.hi + 1):
        b = base[rank - 1] if rank <= len(base) else None
        m = model[rank - 1] if rank <= len(model) else None
        i = other[rank - 1] if rank <= len(other) else None
        ranks.append({"rank": rank, "now": b, "modelled": m, "isabelle": i,
                      "now_ratio": b / i if b and i else None,
                      "modelled_ratio": m / i if m and i else None})
        if b and i:
            worst_now = max(worst_now, b / i)
        if m and i:
            worst_model = max(worst_model, m / i)

    print(f"placement {args.placement}; hex solved {len(base)} -> {len(model)}, "
          f"isabelle {len(other)}")
    print(f"records: {hex_sweep.name}, {isabelle_sweep.name}, {CERTIFICATE.name}")
    print()
    print("| rank | now | modelled | isabelle | now / isa | modelled / isa |")
    print("|---:|---:|---:|---:|---:|---:|")
    for row in ranks:
        nr = f"{row['now_ratio']:.2f}x" if row["now_ratio"] else "--"
        mr = f"{row['modelled_ratio']:.2f}x" if row["modelled_ratio"] else "--"
        print(f"| {row['rank']} | {fmt(row['now'])} | {fmt(row['modelled'])} | "
              f"{fmt(row['isabelle'])} | {nr} | {mr} |")
    print()
    print(f"worst ratio over ranks {args.lo}--{args.hi}: "
          f"now {worst_now:.3f}x, modelled {worst_model:.3f}x")
    unpriced = [r["name"] for r in replacements if not r["priced"]]
    if unpriced:
        print(f"left at their measured time (no phase profile): "
              f"{', '.join(unpriced)}")
    print()
    for row in replacements:
        if row["priced"]:
            print(f"  {row['name']:16s} {fmt(row['now_seconds']):>10s} -> "
                  f"{fmt(row['modelled_seconds']):>10s}   "
                  f"(retained {row['retained_nanos'] / 1e6:.3f} ms + "
                  f"certificate {row['certificate_nanos'] / 1e3:.1f} us)")

    if args.output:
        Path(args.output).write_text(json.dumps({
            "schema": "hexbz-quadratic-norm-cactus-model/1",
            "env": {
                "git_commit": git("rev-parse", "HEAD"),
                "git_dirty": source_dirty(),
                "hostname": socket.gethostname(),
                "arch": platform.machine(),
                "service_sha256": hashlib.sha256(SERVICE.read_bytes()).hexdigest(),
            },
            "config": {
                "placement": args.placement,
                "retained_phases": list(phases),
                "only": sorted(wanted) if wanted else None,
                "repeats": args.repeats,
                "hex_sweep": hex_sweep.name,
                "isabelle_sweep": isabelle_sweep.name,
                "certificate_record": CERTIFICATE.name,
                "corpus_sha256": corpus_sha,
            },
            "solved": {"now": len(base), "modelled": len(model),
                       "isabelle": len(other)},
            "worst_ratio": {"now": worst_now, "modelled": worst_model,
                            "lo": args.lo, "hi": args.hi},
            "ranks": ranks,
            "replacements": replacements,
        }, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
