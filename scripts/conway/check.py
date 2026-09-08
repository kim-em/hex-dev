#!/usr/bin/env python3
"""Offline input/certificate preflight; this is not Lean proof-budget evidence."""

import json
import time
from pathlib import Path
from generate import HERE, ROOT, factors, power, add, mul, div, cert


def main():
    rows = json.loads((HERE / "candidates.json").read_text())["entries"]
    data = {(r["p"], r["n"]): r["coeffs"] for r in rows}
    shared = json.loads(
        (ROOT / "scripts/oracle/luebeck_conway_cache.json").read_text()
    )["entries"]
    for row in shared:
        key = (row["p"], row["n"])
        if key in data:
            assert row["coeffs"] == data[key], (key, "shared corpus cache differs")
    result = []
    for p, n in data:
        start = time.monotonic()
        f = data[p, n]
        order = p**n - 1
        assert power([0, 1], order, f, p) == [1], (p, n, "full power")
        qs = [q for q, e in factors(order)] if order > 1 else []
        assert all(power([0, 1], order // q, f, p) != [1] for q in qs), (
            p,
            n,
            "primitive",
        )
        ds = [m for m in range(1, n) if n % m == 0]
        for m in ds:
            x = power([0, 1], order // (p**m - 1), f, p)
            v = []
            for c in reversed(data[p, m]):
                v = div(add(mul(v, x, p), [c], p), f, p)[1]
            assert not v, (p, m, n, "compatibility")
        source = cert(p, n, f)
        result.append(
            dict(
                p=p,
                n=n,
                proper_divisors=ds,
                order_factors=factors(order) if order > 1 else [],
                largest_factor_bits=max(qs, default=1).bit_length(),
                rabin_source_bytes=len(source.encode()),
                python_preflight_seconds=time.monotonic() - start,
            )
        )
    (ROOT / "reports/conway/preflight.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )
    print(f"Preflight passed for all {len(result)} available candidates", flush=True)


if __name__ == "__main__":
    main()
