#!/usr/bin/env python3
"""Run the cross-implementation canonical-labelling sweep under a
per-instance time budget.

Each implementation gets its own process per instance, so that an
instance's budget is spent on the one measurement being judged, and so
that a search which does not terminate can be killed rather than waited
on. Two things make an instance unsolved for an implementation:

* the process is killed at ``--kill`` seconds of wall clock, or
* it reports a per-call time above ``--budget`` seconds.

The first catches non-termination — `IsoGraph.Canon.canonical` does not
finish PG(2,11) in twenty minutes — and the second is the actual rule:
no single canonical labelling may take longer than the budget. The wall
kill is set well above the budget because it also has to cover process
start-up, reading the instance, and the warm-up call the drivers make
before timing.

**Give-up rule.** Within a family, instances are run in increasing size
and an implementation that fails one is not offered any larger instance
of that family. These families are monotone in difficulty, so continuing
would only spend the wall kill again for the same answer.

Output is one merged JSON line per instance with a `null` for every
column that went unsolved, which the plotting script reads as an
instance that curve did not reach.

    python3 scripts/bench/graphiso_corpus.py --split corpus/ \\
        --max-n 3072 --max-hard-n 2048
    python3 scripts/bench/graphiso_sweep.py --corpus corpus/ \\
        --isograph /path/to/IsoGraph --out merged.jsonl
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# (column key, produced fields, how to build the command)
COLUMNS = [
    ("hex-canon", ["fast_ns", "nodes"]),
    ("hex-run", ["search_ns"]),
    ("hex-ffi", ["nauty_ffi_ns"]),
    ("iso-canon", ["iso_ns", "iso_nodes"]),
    ("iso-whole", ["iso_whole_ns"]),
    ("nauty", ["nauty_ns", "nauty_whole_ns", "nauty_nodes"]),
    ("sparse", ["sparse_ns", "sparse_whole_ns", "sparse_nodes"]),
    ("traces", ["traces_ns", "traces_whole_ns", "traces_nodes"]),
]

# the field each column is judged on, for the budget test
JUDGED = {
    "hex-canon": "fast_ns", "hex-run": "search_ns", "hex-ffi": "nauty_ffi_ns",
    "iso-canon": "iso_ns", "iso-whole": "iso_whole_ns", "nauty": "nauty_ns",
    "sparse": "sparse_ns", "traces": "traces_ns",
}


def _pin(args) -> list[str]:
    """`taskset` prefix pinning a measurement to one CPU.

    SPEC/benchmarking.md asks for a measurement to be pinned to one
    automatically selected CPU where the runner supports it, so that two
    Hex measurements running at once do not land on the same one. The
    CPU is chosen once per sweep from the process id; it need not be
    idle."""
    if args.cpu is None or not shutil.which("taskset"):
        return []
    return ["taskset", "-c", str(args.cpu)]


def _command(column: str, path: Path, args) -> list[str]:
    hexbin = REPO_ROOT / ".lake/build/bin/hexgraphiso_cactus"
    isobin = Path(args.isograph) / ".lake/build/bin/hexcompare"
    prefix = _pin(args)
    return prefix + {
        "hex-canon": [str(hexbin), "read", str(path), "canon"],
        "hex-run": [str(hexbin), "read", str(path), "run"],
        "hex-ffi": [str(hexbin), "read", str(path), "ffi"],
        "iso-canon": [str(isobin), str(path), "canon"],
        "iso-whole": [str(isobin), str(path), "whole"],
        "nauty": [str(args.nauty), str(path), "dense"],
        "sparse": [str(args.nauty), str(path), "sparse"],
        "traces": [str(args.nauty), str(path), "traces"],
    }[column]


def _wall(n: int, args) -> float:
    """The wall-clock kill for an instance on `n` vertices."""
    return args.kill + args.kill_per_1000 * n / 1000.0


def _run(column: str, path: Path, n: int, args) -> tuple[dict | None, str]:
    """Run one column on one instance. Returns (fields, status)."""
    try:
        proc = subprocess.run(_command(column, path, args),
                              capture_output=True, text=True,
                              timeout=_wall(n, args))
    except subprocess.TimeoutExpired:
        return None, "killed"
    if proc.returncode != 0:
        print(f"    {column} failed on {path.name}: "
              f"{proc.stderr.strip()[:200]}", file=sys.stderr)
        return None, "failed"
    line = next((l for l in proc.stdout.splitlines() if l.startswith("{")),
                None)
    if line is None:
        return None, "no output"
    record = json.loads(line)
    judged = record.get(JUDGED[column])
    if judged is not None and judged / 1e9 > args.budget:
        return record, "over budget"
    return record, "ok"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True,
                        help="directory written by graphiso_corpus.py --split")
    parser.add_argument("--isograph", required=True,
                        help="an IsoGraph checkout with `hexcompare` built")
    parser.add_argument("--nauty", default="/tmp/nautybench",
                        help="the standalone nauty driver")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--budget", type=float, default=5.0,
                        help="seconds; a reported per-call time above this "
                             "counts as unsolved")
    parser.add_argument("--kill", type=float, default=20.0,
                        help="base seconds of wall clock before the process "
                             "is killed, covering start-up and the warm-up "
                             "call; see --kill-per-1000 for the size term")
    parser.add_argument("--kill-per-1000", type=float, default=15.0,
                        help="extra wall seconds per thousand vertices. The "
                             "drivers read the instance and make a warm-up "
                             "call before timing anything, and both grow "
                             "with n, so a flat wall kills large instances "
                             "whose search is well inside the budget: at "
                             "n = 3072 a flat 25 s killed searches taking "
                             "4.7 s.")
    parser.add_argument("--passes", type=int, default=2)
    parser.add_argument("--cpu", type=int, default=None,
                        help="pin every measurement to this CPU; the "
                             "default picks one from the process id")
    parser.add_argument("--no-pin", action="store_true",
                        help="do not pin to a CPU")
    parser.add_argument("--only", default=None,
                        help="comma-separated `column:family` pairs to run, "
                             "for re-measuring part of a sweep")
    parser.add_argument("--merge-into", type=Path, default=None,
                        help="an existing merged file to update in place "
                             "rather than starting from nothing")
    args = parser.parse_args()

    if args.no_pin:
        args.cpu = None
    elif args.cpu is None:
        args.cpu = os.getpid() % (os.cpu_count() or 1)
        print(f"pinning measurements to CPU {args.cpu}", file=sys.stderr)

    index = [json.loads(l) for l in
             (args.corpus / "index.jsonl").read_text().splitlines() if l]
    families: dict[str, list[dict]] = {}
    for entry in index:
        families.setdefault(entry["family"], []).append(entry)
    for group in families.values():
        group.sort(key=lambda e: e["n"])

    only = None
    if args.only:
        only = {tuple(pair.split(":", 1)) for pair in args.only.split(",")}

    best: dict[str, dict] = {}
    if args.merge_into is not None:
        for line in args.merge_into.read_text().splitlines():
            if line:
                r = json.loads(line)
                best[r["name"]] = r
    status: dict[tuple[str, str], str] = {}
    # a family an implementation has already lost is not offered again, in
    # this pass or any later one: rediscovering it costs another wall kill
    # for the same answer
    gaveup: set[tuple[str, str]] = set()
    for p in range(args.passes):
        started = time.time()
        for family, group in sorted(families.items()):
            for entry in group:
                name = entry["name"]
                row = best.setdefault(
                    name, {"family": family, "name": name, "n": entry["n"]})
                for column, fields in COLUMNS:
                    if only is not None and (column, family) not in only:
                        continue
                    if (column, family) in gaveup:
                        status.setdefault((column, name), "skipped")
                        continue
                    record, st = _run(column, Path(entry["path"]),
                                      entry["n"], args)
                    if st != "ok":
                        gaveup.add((column, family))
                        status[(column, name)] = st
                        print(f"  {name} ({family}, n={entry['n']}): "
                              f"{column} {st}; giving up on this family",
                              file=sys.stderr)
                        continue
                    status[(column, name)] = "ok"
                    for f in fields:
                        if f in record:
                            prev = row.get(f)
                            row[f] = (min(prev, record[f])
                                      if f.endswith("_ns") and prev is not None
                                      else record[f])
        print(f"pass {p + 1} done in {time.time() - started:.0f}s",
              file=sys.stderr)

    for row in best.values():
        for column, fields in COLUMNS:
            for f in fields:
                row.setdefault(f, None)
    rows = sorted(best.values(), key=lambda r: (r["family"], r["n"]))
    args.out.write_text("".join(json.dumps(r) + "\n" for r in rows))

    solved = {c: sum(1 for r in rows if r[JUDGED[c]] is not None)
              for c, _ in COLUMNS}
    print(f"\n{len(rows)} instances; solved within {args.budget:g} s:",
          file=sys.stderr)
    for column, _ in COLUMNS:
        print(f"  {column:10} {solved[column]:4}/{len(rows)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
