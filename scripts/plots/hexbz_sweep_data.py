#!/usr/bin/env python3
"""Shared reader for the cross-system factorization sweep records.

`scripts/plots/hexbz-cactus.py` (figures) and `scripts/bench/cactus_rank_table.py`
(rank tables) must agree byte-for-byte about which measurement of each system is
current, so the record-selection rule lives here once. This module imports only
the standard library, so the rank table does not need matplotlib.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
BENCH_RESULTS = ROOT / "reports" / "bench-results"

# Canonical system order, so a legend or a table column set is stable.
SYSTEM_ORDER = [
    "hex-factor",
    "hex-lattice",
    "hex-classical-nodecline",
    "flint",
    "ntl",
    "pari",
    "isabelle-bz",
    "isabelle-lll",
]

# Systems the current-state charts and tables publish. Retired standalone Hex
# diagnostic comparators are excluded unless a record naming them is passed
# explicitly.
CURRENT_SYSTEMS = {
    "hex-factor", "flint", "ntl", "pari", "isabelle-bz", "isabelle-lll"
}


def load_corpus(path: Path = CORPUS_PATH):
    info = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        info[rec["name"]] = {"family": rec["family"], "degree": rec["degree"],
                             "combined": rec.get("combined", False)}
    return info


def corpus_sha256(path: Path = CORPUS_PATH) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def default_sweep_paths():
    """Return committed sweep records whose corpus hash matches today's corpus."""
    wanted = corpus_sha256()
    candidates = sorted(BENCH_RESULTS.glob("hexbz-factor-sweep-*.json"))
    paths = []
    for path in candidates:
        report_sha = json.loads(path.read_text()).get("config", {}).get("corpus_sha256")
        if report_sha == wanted:
            paths.append(path)
    return paths, len(candidates) - len(paths)


def merge_reports(paths):
    """Merge several sweep records, taking the NEWEST measurement of each system.

    This is what lets the Lean entries be re-run cheaply without re-running the
    expensive external comparators: point the reader at the fresh hex-only record
    plus the committed baseline, and each system's curve comes from whichever
    record measured it most recently. All records must cover the same corpus
    (matching `corpus_sha256`), since a system's solved-set is only comparable
    against the same instances.

    Returns (results, systems, provenance, cutoffs). `systems` is ordered by the
    canonical `SYSTEM_ORDER` for a stable legend; `provenance[system]` is
    (record filename, ISO timestamp, cutoff).
    """
    reports = [(pth, json.loads(pth.read_text())) for pth in paths]
    shas = {r["config"]["corpus_sha256"] for _, r in reports}
    if len(shas) > 1:
        raise SystemExit(
            "refusing to merge sweeps over different corpora (corpus_sha256 "
            "mismatch); re-run the external systems against the current corpus")
    chosen = {}  # system -> (ts, filename, iso, cutoff, results)
    for pth, rep in reports:
        ts = rep["env"].get("timestamp_unix_ms") or 0
        iso = rep["env"].get("timestamp_iso")
        cutoff = rep["config"]["cutoff_seconds"]
        for system in rep["config"]["systems"]:
            if system not in chosen or ts > chosen[system][0]:
                sysres = [r for r in rep["results"] if r["system"] == system]
                chosen[system] = (ts, pth.name, iso, cutoff, sysres)
    results, provenance, cutoffs = [], {}, set()
    for system, (_, fname, iso, cutoff, sysres) in chosen.items():
        results.extend(sysres)
        provenance[system] = (fname, iso, cutoff)
        cutoffs.add(cutoff)
    systems = sorted(
        chosen,
        key=lambda s: SYSTEM_ORDER.index(s) if s in SYSTEM_ORDER else len(SYSTEM_ORDER))
    return results, systems, provenance, cutoffs
