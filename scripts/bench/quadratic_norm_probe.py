#!/usr/bin/env python3
"""Price the iterated-quadratic-norm irreducibility certificate (issue #9133).

Two measurements, one durable record.

*Hits.* ``hexbz_factor_service --entry quadraticNormProbe`` runs one production
factorization and the four certificate stages -- radicand recovery, the
square-class independence test, the iterated-norm coefficient construction, and
the equality test -- on the same input in the same process. Both sides of the
reported ratio come from those same observations, so it is a paired ratio and
not two runs subtracted. Rows the production cascade does not finish are
measured with ``--entry quadraticNormCertificate``, which runs the certificate
stages alone; their production side is recorded as ``null``.

Since the certificate is now *on* the production path, the paired ratio
``paired_production_over_certificate`` is no longer a speedup: for a certified
row the production call runs the certificate too, so the ratio says what share
of the integrated row the certificate is. The before/after speedup lives in the
factor sweep, not here.

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

# Extra rows to pair even when the sweep record does not list them as solved.
# Everything the production cascade does not finish inside the sweep cutoff is
# measured certificate-only instead, and says so in the record. Since the
# certificate went onto the production path this set is normally redundant: the
# rows it named are now solved and the sweep lists them.
PAIRED_UNSOLVED = ("sd6_shift1",)


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


def newest_hex_sweep(corpus_sha: str) -> Path:
    """The newest committed hex-factor sweep measured against this corpus."""
    candidates = []
    for path in (ROOT / "reports" / "bench-results").glob(
            "hexbz-factor-sweep-*.json"):
        record = json.loads(path.read_text())
        if record.get("config", {}).get("corpus_sha256") != corpus_sha:
            continue
        if "hex-factor" not in record.get("config", {}).get("systems", []):
            continue
        candidates.append(
            (record.get("env", {}).get("timestamp_unix_ms", 0), path))
    if not candidates:
        raise SystemExit("no hex-factor sweep matches the current corpus")
    return max(candidates)[1]


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True)
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--sweep", type=Path,
                        help="sweep record naming the rows to measure paired; "
                             "defaults to the newest matching this corpus")
    args = parser.parse_args(argv[1:])

    if not SERVICE.exists():
        raise SystemExit(f"missing {SERVICE}; run `lake build hexbz_factor_service`")
    corpus = load_corpus()

    # Which rows get a paired production run: everything the sweep solves, plus
    # any row this driver is told to measure anyway. A row the sweep does not
    # solve would spend the whole run inside one production call.
    corpus_sha = hashlib.sha256(CORPUS.read_bytes()).hexdigest()
    solved = set(PAIRED_UNSOLVED)
    sweep = args.sweep or newest_hex_sweep(corpus_sha)
    record = json.loads(sweep.read_text())
    if record["config"]["corpus_sha256"] != corpus_sha:
        raise SystemExit(f"{sweep.name}: measured against a different corpus")
    if "hex-factor" not in record["config"]["systems"]:
        raise SystemExit(f"{sweep.name}: carries no hex-factor curve")
    for row in record["results"]:
        if row["system"] == "hex-factor" and row["status"] == "ok":
            solved.add(row["name"])
    print(f"paired rows taken from {sweep.name} "
          f"({len(solved)} solved, cutoff {record['config']['cutoff_seconds']}s)",
          file=sys.stderr)

    hits, misses = [], []
    for name, row in corpus.items():
        paired = name in solved
        # A paired call costs a full production factorization, so the first,
        # classifying observation always uses the certificate-only entry.
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
                # under a second, a single call otherwise. Both sides of the
                # ratio are then read off these same observations, so the two
                # spans describe one execution rather than two runs.
                observations = ask("quadraticNormProbe", [row["coeffs"]])
                if observations[0]["production"]["nanos"] < 1e9:
                    observations = ask("quadraticNormProbe",
                                       [row["coeffs"]] * args.repeats)
                ratios = sorted(o["production"]["nanos"] / max(
                    certificate_nanos(o), 1) for o in observations)
                record["production"] = {
                    "nanos": int(statistics.median(
                        o["production"]["nanos"] for o in observations)),
                    "smallAllocs": int(statistics.median(
                        o["production"]["smallAllocs"] for o in observations)),
                }
                record["paired_certificate_nanos"] = int(statistics.median(
                    certificate_nanos(o) for o in observations))
                record["paired_production_over_certificate"] = statistics.median(ratios)
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
            "git_dirty": source_dirty(),
            "hostname": socket.gethostname(),
            "arch": platform.machine(),
            "corpus_sha256": hashlib.sha256(CORPUS.read_bytes()).hexdigest(),
            "service_sha256": hashlib.sha256(SERVICE.read_bytes()).hexdigest(),
        },
        "config": {
            "repeats": args.repeats,
            "paired_sweep": sweep.name,
            "statistic": "median over repeats, span by span; "
                         "`paired_production_over_certificate` is the median "
                         "of the per-observation ratios",
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
            print(f"  {r['name']:16s} {r['production']['nanos'] / 1e6:10.3f} ms "
                  f"-> {r['paired_certificate_nanos'] / 1e3:8.1f} us  "
                  f"(certificate is 1/{r['paired_production_over_certificate']:.0f} "
                  f"of the paired row)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
