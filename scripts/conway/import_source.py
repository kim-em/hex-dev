#!/usr/bin/env python3
"""Refresh the expansion study inputs, without changing the factor corpus cache."""

import ast
import hashlib
import json
from pathlib import Path
import urllib.request

URL = "https://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CPimport.txt"


def main():
    raw = urllib.request.urlopen(URL, timeout=60).read()
    text = raw.decode("latin1")
    rows = ast.literal_eval(text[text.index("[") : text.rindex("]") + 1])
    data = {}
    for p, n, coeffs in rows:
        if (p, n) in data:
            raise ValueError(f"Duplicate source entry: {(p, n)}")
        if (
            not isinstance(p, int)
            or not isinstance(n, int)
            or p < 2
            or n < 1
            or len(coeffs) != n + 1
            or coeffs[-1] != 1
            or any(not isinstance(c, int) or not 0 <= c < p for c in coeffs)
        ):
            raise ValueError(f"Malformed source entry: {(p, n)}")
        data[p, n] = coeffs
    primes = [
        p for p in range(2, 1000) if all(p % d for d in range(2, int(p**0.5) + 1))
    ]
    keys = [
        (p, n)
        for p in primes
        for n in range(1, (32 if p == 2 else 16 if p < 11 else 8 if p < 100 else 4) + 1)
    ] + [(2, 64), (2, 128)]
    result = dict(
        source=URL,
        source_sha256=hashlib.sha256(raw).hexdigest(),
        coefficient_order="ascending",
        entries=[dict(p=p, n=n, coeffs=data[p, n]) for p, n in keys if (p, n) in data],
        unavailable=[list(k) for k in keys if k not in data],
    )
    Path(__file__).with_name("candidates.json").write_text(
        json.dumps(result, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
