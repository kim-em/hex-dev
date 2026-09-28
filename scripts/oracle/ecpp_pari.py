#!/usr/bin/env python3
"""Independent affine replay plus PARI primality checks for HexECPP JSONL."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys


def add(n: int, a: int, p, q, witnesses: list[int]):
    if p is None:
        return {"point": q, "rest": witnesses}
    if q is None:
        return {"point": p, "rest": witnesses}
    x1, y1 = p
    x2, y2 = q
    if x1 == x2 and (y1 + y2) % n == 0:
        return {"point": None, "rest": witnesses}
    if x1 == x2:
        if y1 != y2:
            return None
        d = (2 * y1) % n
        v = (3 * x1 * x1 + a) % n
    else:
        d = (x2 - x1) % n
        v = (y2 - y1) % n
    if not witnesses:
        return None
    u = witnesses[0]
    try:
        inverse = pow(d, -1, n)
    except ValueError:
        return None
    if not (0 <= u < n and u == inverse):
        return None
    slope = v * inverse % n
    x3 = (slope * slope - x1 - x2) % n
    y3 = (slope * (x1 - x3) - y1) % n
    return {"point": [x3, y3], "rest": witnesses[1:]}


def check_step(row: dict) -> bool:
    n, a, b, x, y, d, q = (row[k] for k in "n a b x y d q".split())
    if not (n > 3 and n % 6 in (1, 5) and 2 <= q < n):
        return False
    if not all(0 <= z < n for z in (a, b, x, y, d)):
        return False
    if (y * y - x * x * x - a * x - b) % n != 0:
        return False
    if (4 * a**3 + 27 * b**2) * d % n != 1:
        return False
    c = (q - 1) ** 2 - n
    if not (c > 0 and 16 * n * q < c * c):
        return False
    base = [x, y]
    point = None
    witnesses = row["witnesses"]
    for bit in reversed(range(q.bit_length())):
        out = add(n, a, point, point, witnesses)
        if out is None:
            return False
        point, witnesses = out["point"], out["rest"]
        if (q >> bit) & 1:
            out = add(n, a, point, base, witnesses)
            if out is None:
                return False
            point, witnesses = out["point"], out["rest"]
    return point is None and not witnesses


def scalar(n: int, a: int, q: int, base, witnesses: list[int]):
    point = None
    for bit in reversed(range(q.bit_length())):
        out = add(n, a, point, point, witnesses)
        if out is None:
            return None
        point, witnesses = out["point"], out["rest"]
        if (q >> bit) & 1:
            out = add(n, a, point, base, witnesses)
            if out is None:
                return None
            point, witnesses = out["point"], out["rest"]
    # Hex's bitLength visits one zero bit when q = 0; doubling infinity
    # consumes no witness and leaves the same result.
    return {"point": point, "rest": witnesses}


def pari_isprime(n: int) -> bool:
    try:
        from cypari2 import Pari

        return bool(int(Pari().isprime(n)))
    except ImportError:
        gp = shutil.which("gp") or os.environ.get("HEX_PARI_GP")
        if not gp:
            raise RuntimeError("PARI is required: install cypari2 or set HEX_PARI_GP")
        result = subprocess.run(
            [gp, "-q"],
            input=f"print(isprime({n}))\n\\q\n",
            text=True,
            capture_output=True,
            check=True,
        )
        return result.stdout.strip().splitlines()[-1] == "1"


def _gp_point(point) -> str:
    return "[0]" if point is None else f"[{point[0]},{point[1]}]"


def pari_group_check(rows: list[dict]) -> None:
    """Cross-check every accepted small-field operation with PARI's group law."""
    gp = shutil.which("gp") or os.environ.get("HEX_PARI_GP")
    if not gp:
        raise RuntimeError("PARI gp is required for elliptic-curve oracle checks")
    commands = []
    expected = []
    curve = None
    for row in rows:
        kind = row["kind"]
        if kind not in ("add", "scalar", "step", "curve") or (row.get("result") is None and kind not in ("step", "curve")):
            continue
        key = (row["n"], row["a"], row["b"])
        if key != curve:
            n, a, b = key
            commands.append(f"E=ellinit([0,0,0,{a},{b}],{n});")
            curve = key
        if kind == "curve":
            commands.append("print([lift(E.j),ellcard(E)]);")
            expected.append([row["j"], row["order"]])
        elif kind == "add":
            commands.append(
                f"print(lift(elladd(E,{_gp_point(row['p'])},{_gp_point(row['q'])})));"
            )
            expected.append(row["result"]["point"])
        elif kind == "scalar":
            commands.append(
                f"print(lift(ellmul(E,{_gp_point(row['point'])},{row['q']})));"
            )
            expected.append(row["result"]["point"])
        elif row["accepted"]:
            commands.append(
                f"print(lift(ellmul(E,[{row['x']},{row['y']}],{row['q']})));"
            )
            expected.append(None)
    source = "\n".join(commands) + "\n\\q\n"
    result = subprocess.run(
        [gp, "-q"], input=source, text=True, capture_output=True, check=True
    )
    actual = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    assert len(actual) == len(expected), (len(actual), len(expected), result.stderr)
    for i, (got, want) in enumerate(zip(actual, expected, strict=True)):
        normalized = None if got == [0] else got
        assert normalized == want, (i, normalized, want)


def jacobi(a: int, n: int) -> int:
    sign = 1
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        if a % 4 == n % 4 == 3:
            sign = -sign
        a, n = n % a, a
    return sign if n == 1 else 0


def main() -> int:
    rows = [json.loads(line) for line in sys.stdin if line.strip()]
    for row in rows:
        kind = row["kind"]
        if kind == "curve":
            n, a, b = (row[k] for k in ("n", "a", "b"))
            order = 1 + sum((y*y - x*x*x - a*x - b) % n == 0
                            for x in range(n) for y in range(n))
            assert row["order"] == order, row
            assert row["j"] == 1728*4*a**3*pow(4*a**3+27*b*b, -1, n) % n, row
            continue
        if kind == "root":
            n, a, root = row["n"], row["a"], row["root"]
            assert row["symbol"] == jacobi(a, n), row
            if root is not None:
                assert 0 <= root < n and root * root % n == a % n, row
            continue
        if kind == "norm":
            if row["result"] is not None:
                t, v = row["result"]
                assert t * t + row["d"] * v * v == 4 * row["n"], row
            continue

        if kind == "add":
            got = add(row["n"], row["a"], row["p"], row["q"], row["witnesses"])
            assert got == row["result"], row
        elif kind == "scalar":
            got = scalar(row["n"], row["a"], row["q"], row["point"], row["witnesses"])
            assert got == row["result"], row
        elif kind == "step":
            assert check_step(row) == row["accepted"], row
            assert pari_isprime(row["q"]), row
        elif kind == "subject":
            assert pari_isprime(row["n"]) == row["accepted"], row
        else:
            raise AssertionError(f"unsupported fixture kind: {kind}")
    pari_group_check(rows)
    print(f"HexECPP: {len(rows)} independent cases passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
