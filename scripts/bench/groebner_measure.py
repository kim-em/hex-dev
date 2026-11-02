#!/usr/bin/env python3
"""Retain shared-host lean-bench samples for the portable F4 candidate engine.

Stage measured sources first. Each source/benchmark observation is immutable;
use --repeat once for an unchanged inconclusive observation. Fixed systems time
candidate production through final interreduction, excluding input generation,
certification and kernel checking. The interning registration uses its declared
fixed trial-major schedule. No host-activity observation rejects a sample.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease
from scripts.bench.sweep_freshness import Family, fingerprint, index_listing

FAMILY = Family(
    name="hexgroebner-f4",
    include=("HexGroebner/", "HexGroebner.lean", "HexGroebnerNative.lean", "HexGroebnerMatrixNative.lean", "HexGroebnerTrieNative.lean", "HexGroebnerMonomialNative.lean", "HexGroebnerEliminationNative.lean", "HexArith/", "HexArith.lean",
             "HexArithNative.lean", "HexModArith/", "HexModArith.lean",
             "HexModArithNative.lean", "HexBasic/", "HexBasic.lean", "HexMvPoly/",
             "HexMvPoly.lean", "bench/HexGroebner/", "lakefile.lean",
             "lake-manifest.json", "lean-toolchain", "scripts/bench/groebner_measure.py", "scripts/bench/groebner_cli_measure.py", "scripts/bench/groebner_freeze.py", "scripts/bench/cpu_lease.py",
             "scripts/oracle/groebner_singular.py", "scripts/oracle/common.py",
             "scripts/bench/sweep_freshness.py"),
    exclude=("HexGroebner/README.md", "HexArith/README.md", "HexModArith/README.md",
             "HexMvPoly/README.md", "HexArith/SPEC/", "HexModArith/SPEC/", "HexMvPoly/SPEC/"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("benchmark", choices=("internMonomials", "cyclic4", "cyclic5", "cyclic6", "katsura3"))
    parser.add_argument("--repeat", action="store_true")
    args = parser.parse_args()
    os.chdir(ROOT)
    changed = subprocess.check_output(["git", "diff", "--name-only"], text=True).splitlines()
    untracked = subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard"], text=True).splitlines()
    if any(FAMILY.matches(path) for path in changed + untracked):
        parser.error("stage every measured source before fingerprinting")
    listing = index_listing(FAMILY)
    digest = fingerprint(listing)
    base = ROOT / "reports/bench-results" / f"hexgroebner-{args.benchmark}-{digest}"
    if args.repeat:
        if not base.with_suffix(".json").exists():
            parser.error("an unchanged repeat requires an existing first observation")
        base = base.with_name(base.name + "-repeat")
    if any(base.with_suffix(suffix).exists() for suffix in (".json", ".log", ".manifest")):
        parser.error("preserve existing observation; at most one unchanged repeat is supported")
    subprocess.run(["lake", "build", "hexgroebner_bench"], check=True)
    base.with_suffix(".manifest").write_text(listing)
    cpu, lease = cpu_lease()
    try:
        os.sched_setaffinity(0, {cpu})
        binary = ROOT / ".lake/build/bin/hexgroebner_bench"
        command = [str(binary), "run", f"Hex.Groebner.Bench.{args.benchmark}"]
        if args.benchmark == "internMonomials":
            command += ["--outer-trials", "3"]
        command += ["--export-file", str(base.with_suffix(".json"))]
        metadata = dict(source_fingerprint=digest, include=FAMILY.include, exclude=FAMILY.exclude,
                        cpu=cpu, affinity=sorted(os.sched_getaffinity(0)), threads=1,
                        host=os.uname().nodename, toolchain=Path("lean-toolchain").read_text().strip(),
                        command=command, load_start=os.getloadavg(),
                        binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                        schedule="declared lean-bench schedule; all completed samples retained",
                        contract="candidate only; input generation, certification and kernel checking excluded")
        start = time.monotonic()
        with base.with_suffix(".log").open("w") as output:
            result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT)
        metadata.update(returncode=result.returncode, elapsed_seconds=time.monotonic() - start,
                        load_end=os.getloadavg(),
                        peak_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
        base.with_suffix(".measurement.json").write_text(json.dumps(metadata, indent=2) + "\n")
        print(base.relative_to(ROOT))
        print(base.with_suffix(".log").read_text())
        return result.returncode
    finally:
        lease.close()


if __name__ == "__main__":
    sys.exit(main())
