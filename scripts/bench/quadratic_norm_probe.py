#!/usr/bin/env python3
"""Price the iterated-quadratic-norm irreducibility certificate (issue #9133).

Two measurements, one durable record.

*Hits.* ``hexbz_factor_service --entry quadraticNormProbe`` runs one production
factorization and the four certificate stages -- radicand recovery, the
square-class independence test, the iterated-norm coefficient construction, and
the equality test -- on the same input in the same process, so the speedup is a
paired ratio rather than two sweeps subtracted. Rows the production cascade does
not finish are measured with ``--entry quadraticNormCertificate``, which runs
the certificate stages alone; their production side is recorded as ``null``.

*Misses.* The certificate-only entry is then swept across the whole corpus. A
row that declines pays only the recovery span, and that span is the overhead a
budget-gated production attempt would add. Recording it for every row -- not
just the ones expected to decline -- is what makes the miss claim a measurement.

Each measured span is the median of ``--repeats`` calls, so an unlucky page
fault does not become the reported number.

This is a diagnostic driver, not a benchmark harness: it emits raw spans for
``reports/hexbz-quadratic-norm-certificate.md`` and no merge-gating suite runs
it.

Run::

    lake build hexbz_factor_service
    taskset -c 0 python3 scripts/bench/quadratic_norm_probe.py \\
        --output reports/bench-results/hexbz-quadratic-norm-certificate.json
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
SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"

STAGES = ("recovery", "independence", "construction", "equality")

# Rows whose production factorization the paired probe runs. Everything the
# production cascade does not finish inside the sweep cutoff is measured
# certificate-only instead, and says so in the record.
PAIRED_UNSOLVED = ("sd6_shift1",)


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, text=True,
                          capture_output=True, check=True).stdout.strip()


def load_corpus() -> dict:
    corpus = {}
    for line in CORPUS.read_text().splitlines():
        if line.strip():
            row = json.loads(line)
            corpus[row["name"]] = row
    return corpus


def ask(entry: str, requests: list[list[int]]) -> list[dict]:
    """One warm service process, one reply per request."""
    payload = "".join(json.dumps({"coeffs": c}) + "\n" for c in requests)
    completed = subprocess.run([str(SERVICE), "--entry", entry], input=payload,
                               text=True, capture_output=True, check=True)
    replies = [json.loads(line) for line in completed.stdout.splitlines()
               if line.strip()]
    if len(replies) != len(requests):
        raise SystemExit(f"{entry}: expected {len(requests)} replies, "
                         f"got {len(replies)}")
    return [reply.get("result") or {} for reply in replies]


def median_spans(entry: str, coeffs: list[int], repeats: int) -> dict:
    """Median of `repeats` observations, span by span."""
    observations = ask(entry, [coeffs] * repeats)
    merged = dict(observations[-1])
    for key in ("production", *STAGES):
        present = [o[key] for o in observations if key in o]
        if not present:
            merged.pop(key, None)
            continue
        merged[key] = {
            "nanos": int(statistics.median(s["nanos"] for s in present)),
            "smallAllocs": int(statistics.median(
                s["smallAllocs"] for s in present)),
        }
    merged.pop("witness", None)
    return merged


def certificate_nanos(result: dict) -> int:
    return sum(result[s]["nanos"] for s in STAGES if s in result)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--cutoff-seconds", type=float, default=10.0,
                        help="rows slower than this are measured unpaired")
    args = parser.parse_args(argv[1:])

    if not SERVICE.exists():
        raise SystemExit(f"missing {SERVICE}; run `lake build hexbz_factor_service`")
    corpus = load_corpus()

    # Which rows get a paired production run: everything the committed sweep
    # solves, plus any row this driver is told to measure anyway.
    solved = set(PAIRED_UNSOLVED)
    sweeps = sorted((ROOT / "reports" / "bench-results").glob(
        "hexbz-factor-sweep-*hex*.json"))
    if sweeps:
        newest = max(sweeps, key=lambda path: json.loads(path.read_text())
                     ["env"].get("timestamp_unix_ms", 0))
        for row in json.loads(newest.read_text())["results"]:
            if row["system"] == "hex-factor" and row["status"] == "ok":
                solved.add(row["name"])
        print(f"paired rows taken from {newest.name}", file=sys.stderr)

    hits, misses = [], []
    for name, row in corpus.items():
        paired = name in solved
        entry = "quadraticNormProbe" if paired else "quadraticNormCertificate"
        # A paired call costs a full production factorization, so the sweep-wide
        # miss measurement always uses the certificate-only entry.
        result = median_spans("quadraticNormCertificate", row["coeffs"],
                              args.repeats)
        record = {
            "name": name,
            "family": row["family"],
            "degree": row["degree"],
            "certified": bool(result.get("certified")),
            "translation": result.get("translation"),
            "radicands": result.get("radicands"),
            "certificate_nanos": certificate_nanos(result),
            "spans": {s: result[s] for s in STAGES if s in result},
            "production": None,
            "production_paired": False,
        }
        if record["certified"]:
            if paired:
                # The sweep's own policy: median of `repeats` when one call is
                # under a second, a single call otherwise.
                first = median_spans(entry, row["coeffs"], 1)
                pairedResult = first
                if first["production"]["nanos"] < 1e9:
                    pairedResult = median_spans(entry, row["coeffs"],
                                                args.repeats)
                record["production"] = pairedResult["production"]
                record["production_paired"] = True
            hits.append(record)
        else:
            misses.append(record)
        print(f"  {name:24s} deg={row['degree']:5d} "
              f"{'certified' if record['certified'] else 'declined ':10s} "
              f"{record['certificate_nanos'] / 1e3:9.1f} us", file=sys.stderr)

    record = {
        "schema": "hexbz-quadratic-norm-certificate/1",
        "env": {
            "git_commit": git("rev-parse", "HEAD"),
            "git_dirty": bool(git("status", "--porcelain")),
            "hostname": socket.gethostname(),
            "arch": platform.machine(),
            "corpus_sha256": hashlib.sha256(CORPUS.read_bytes()).hexdigest(),
            "service_sha256": hashlib.sha256(SERVICE.read_bytes()).hexdigest(),
        },
        "config": {
            "repeats": args.repeats,
            "cutoff_seconds": args.cutoff_seconds,
            "statistic": "median over repeats, span by span",
        },
        "hits": sorted(hits, key=lambda r: (r["degree"], r["name"])),
        "misses": sorted(misses, key=lambda r: (r["degree"], r["name"])),
    }
    Path(args.output).write_text(
        json.dumps(record, indent=1, sort_keys=True) + "\n")

    miss = sorted(r["certificate_nanos"] for r in misses)
    print(f"\n{len(hits)} certified, {len(misses)} declined")
    if miss:
        print(f"miss overhead: median {statistics.median(miss) / 1e3:.1f} us, "
              f"max {miss[-1] / 1e3:.1f} us")
    for r in hits:
        if r["production"]:
            ratio = r["production"]["nanos"] / max(r["certificate_nanos"], 1)
            print(f"  {r['name']:16s} {r['production']['nanos'] / 1e6:10.3f} ms "
                  f"-> {r['certificate_nanos'] / 1e3:8.1f} us  ({ratio:.0f}x)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
