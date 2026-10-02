#!/usr/bin/env python3
"""Retain full native factorization samples for explicit SQUFOF examples."""

import argparse
import hashlib
import json
import math
import os
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cpu_lease import cpu_lease

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "oracle"))
from primality_squfof import prime64


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", type=Path, default=Path(".lake/build/bin/hexintfactor_bench"))
    parser.add_argument("--output", type=Path,
                        default=Path("reports/bench-results/hex-int-factor-squfof-examples.jsonl"))
    args = parser.parse_args()
    # Expected factors are independently verified, outside the native timed region.
    cases = [
        ("balanced-56", 40249308338448479, [(184185251, 1), (218526229, 1)], 2, 65536),
        ("close-64", 16212959431627901207, [(4026531853, 1), (4026532019, 1)], 1, 128),
        ("trace-table-control", 22117019, [(4451, 1), (4969, 1)], 1, 25),
        ("table-control", 9797, [(97, 1), (101, 1)], 2, 65536),
        ("prime-control", 100003, [(100003, 1)], 2, 65536),
        ("square-control", 18446744030759878681, [(4294967291, 2)], 2, 65536),
        ("zero-control", 0, [], 2, 65536),
    ]
    for name, n, factors, _, _ in cases:
        if n:
            assert math.prod(p ** e for p, e in factors) == n, name
            assert all(prime64(p) and e > 0 for p, e in factors), name
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # Never overwrite a completed schedule.
    with args.output.open("x") as handle:
        def write(value):
            handle.write(json.dumps(value, separators=(",", ":")) + "\n")
            handle.flush()

        write(dict(type="context", host=platform.node(), platform=platform.platform(),
                   cpu=cpu, load_start=os.getloadavg(), started=datetime.now(timezone.utc).isoformat(),
                   git=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                   source_dirty=bool(subprocess.check_output(["git", "status", "--porcelain"], text=True)),
                   executable_sha256=digest(args.exe),
                   source_sha256={p: digest(p) for p in (
                       "HexIntFactor/Factor.lean", "HexPrimality/Search.lean", "HexPrimality/Squfof.lean",
                       "bench/HexIntFactor/Bench.lean", "scripts/bench/squfof_dispatch.py")},
                   schedule="eight trial-major adjacent off/first pairs, alternating AB/BA, no warmup",
                   timed_region="full counted factorization, certificate construction and checked acceptance",
                   cases=[dict(name=name, n=n, expected=factors, multipliers=mults, steps=steps)
                          for name, n, factors, mults, steps in cases]))
        errors = []
        for trial in range(8):
            for name, n, expected, mults, steps in cases:
                for position, mode in enumerate(("off", "first") if trial % 2 == 0 else ("first", "off")):
                    fuel = 4 * max(0, n.bit_length() - 1) + 32
                    command = [str(args.exe.resolve()), "squfof-factor", str(n), mode,
                               str(mults), str(steps), "128", str(n), str(fuel)]
                    completed = subprocess.run(command, text=True, capture_output=True, timeout=300)
                    # Persist the completed process before checking its output.
                    write(dict(type="process", name=name, trial=trial, position=position,
                               command=command, returncode=completed.returncode,
                               stdout=completed.stdout, stderr=completed.stderr))
                    try:
                        sample = json.loads(completed.stdout)
                        assert completed.returncode == 0
                        assert sample["status"] == ("complete" if n else "Hex.Nat.FactorStop.zero")
                        assert sample["factors"] == [list(pair) for pair in expected]
                        for event in sample["events"]:
                            if event.get("route") == "squfof" and "factor" in event["fields"]:
                                fields = event["fields"]
                                subject, d = int(fields["subject"]), int(fields["factor"])
                                assert 1 < d < subject and subject % d == 0
                        sample.update(type="sample", name=name, trial=trial, position=position)
                        write(sample)
                    except (AssertionError, ValueError, KeyError) as error:
                        errors.append(f"{name}/{trial}/{mode}: {error}")
        write(dict(type="end", finished=datetime.now(timezone.utc).isoformat(),
                   load_end=os.getloadavg(), errors=errors))
        if errors:
            raise RuntimeError("; ".join(errors))
    lease.close()


if __name__ == "__main__":
    main()
