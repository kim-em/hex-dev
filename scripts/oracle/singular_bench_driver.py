#!/usr/bin/env python3
"""Persistent Singular comparator for multivariate GCD benchmarks.

The outer process speaks the repository's one-JSON-request-per-line protocol.
It keeps one quiet Singular subprocess alive and sends it a fresh polynomial
GCD command for each request, so benchmark iterations do not include Singular
startup.  The current family is deliberately narrow: it certifies that the
declared integer inputs are coprime over ``Q[x_1, ..., x_n]``.  That is the
like-for-like family named by ``HexMvGcd``'s informational comparator contract.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from typing import TextIO


def _terms(encoded: object, nvars: int, label: str) -> list[tuple[tuple[int, ...], int]]:
    if not isinstance(encoded, list):
        raise ValueError(f"{label} terms must be a list")
    out: list[tuple[tuple[int, ...], int]] = []
    seen: set[tuple[int, ...]] = set()
    for index, term in enumerate(encoded):
        if not isinstance(term, list) or len(term) != 2:
            raise ValueError(f"{label} term {index} must contain exponents and coefficient")
        exponents, coefficient = term
        if not isinstance(exponents, list) or len(exponents) != nvars:
            actual = len(exponents) if isinstance(exponents, list) else "non-list"
            raise ValueError(
                f"{label} term {index} exponent length {actual}; expected {nvars}"
            )
        if any(not isinstance(exponent, int) or isinstance(exponent, bool)
               for exponent in exponents):
            raise ValueError(f"{label} term {index} has a non-integer exponent")
        if any(exponent < 0 for exponent in exponents):
            raise ValueError(f"{label} term {index} has a negative exponent")
        if not isinstance(coefficient, int) or isinstance(coefficient, bool):
            raise ValueError(f"{label} term {index} coefficient must be an integer")
        key = tuple(exponents)
        if key in seen:
            raise ValueError(f"{label} repeats exponent vector {key}")
        seen.add(key)
        if coefficient != 0:
            out.append((key, coefficient))
    return out


def _poly_expr(terms: list[tuple[tuple[int, ...], int]]) -> str:
    if not terms:
        return "0"
    pieces: list[str] = []
    for exponents, coefficient in terms:
        factors: list[str] = []
        for index, exponent in enumerate(exponents, start=1):
            if exponent == 1:
                factors.append(f"x{index}")
            elif exponent > 1:
                factors.append(f"x{index}^{exponent}")
        monomial = "*".join(factors)
        magnitude = abs(coefficient)
        if not monomial:
            body = str(magnitude)
        elif magnitude == 1:
            body = monomial
        else:
            body = f"{magnitude}*{monomial}"
        if not pieces:
            pieces.append(body if coefficient > 0 else f"-{body}")
        else:
            pieces.append(("+" if coefficient > 0 else "-") + body)
    return "".join(pieces)


class SingularSession:
    def __init__(self, command: str) -> None:
        self._process = subprocess.Popen(
            [command, "-q"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
        )
        if self._process.stdin is None or self._process.stdout is None:
            raise RuntimeError("Singular did not expose piped stdin/stdout")
        self._stdin: TextIO = self._process.stdin
        self._stdout: TextIO = self._process.stdout
        self._nvars: int | None = None
        self._serial = 0

    def _request(self, command: str, expected: str) -> None:
        self._stdin.write(command + "\n")
        self._stdin.flush()
        for line in self._stdout:
            if line.rstrip("\n") == expected:
                return
        raise RuntimeError("Singular closed stdout before the response sentinel")

    def _ensure_ring(self, nvars: int) -> None:
        if self._nvars is None:
            variables = ",".join(f"x{index}" for index in range(1, nvars + 1))
            sentinel = "__HEX_SINGULAR_RING_READY__"
            self._request(
                f'ring hex_ring=0,({variables}),lp; print("{sentinel}");', sentinel
            )
            self._nvars = nvars
        elif self._nvars != nvars:
            raise ValueError(
                f"persistent Singular ring has {self._nvars} variables; requested {nvars}"
            )

    def overhead(self) -> None:
        self._serial += 1
        sentinel = f"__HEX_SINGULAR_OVERHEAD_{self._serial}__"
        self._request(f'print("{sentinel}");', sentinel)

    def gcd_is_one(self, nvars: int, left: str, right: str) -> bool:
        self._ensure_ring(nvars)
        self._serial += 1
        yes = f"__HEX_SINGULAR_GCD_{self._serial}_YES__"
        no = f"__HEX_SINGULAR_GCD_{self._serial}_NO__"
        command = (
            f"poly hex_left={left}; poly hex_right={right}; "
            "poly hex_gcd=gcd(hex_left,hex_right); "
            f'if (hex_gcd==1) {{ print("{yes}"); }} '
            f'else {{ print("{no}"); }} '
            "kill hex_left; kill hex_right; kill hex_gcd;"
        )
        self._stdin.write(command + "\n")
        self._stdin.flush()
        for line in self._stdout:
            answer = line.rstrip("\n")
            if answer == yes:
                return True
            if answer == no:
                return False
        raise RuntimeError("Singular closed stdout before the GCD response sentinel")


def _dispatch(request: dict[str, object], session: SingularSession) -> bool:
    if request.get("family") != "integer_mpoly":
        raise ValueError(f"unknown Singular family: {request.get('family')!r}")
    operation = request.get("op")
    if operation == "overhead":
        session.overhead()
        return True
    if operation != "gcd_is_one":
        raise ValueError(f"unknown Singular integer_mpoly operation: {operation!r}")
    nvars = request.get("nvars")
    if not isinstance(nvars, int) or isinstance(nvars, bool) or nvars <= 0:
        raise ValueError("nvars must be a positive integer")
    left = _poly_expr(_terms(request.get("a"), nvars, "a"))
    right = _poly_expr(_terms(request.get("b"), nvars, "b"))
    if not session.gcd_is_one(nvars, left, right):
        raise ValueError("Singular computed a nonunit GCD for the coprime fixture")
    return True


def main() -> int:
    command = os.environ.get("HEX_SINGULAR_COMMAND", "Singular")
    session: SingularSession | None = None
    for line in sys.stdin:
        try:
            request = json.loads(line)
            if not isinstance(request, dict):
                raise ValueError("request must be a JSON object")
            if session is None:
                session = SingularSession(command)
            result = _dispatch(request, session)
            reply = {"ok": True, "result": result}
        except Exception as error:  # protocol errors are data, not process crashes
            reply = {"ok": False, "error": str(error)}
        print(json.dumps(reply, separators=(",", ":")), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
