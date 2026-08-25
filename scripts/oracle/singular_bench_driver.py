#!/usr/bin/env python3
"""Persistent Singular comparator for multivariate GCD benchmarks.

The outer process speaks the repository's one-JSON-request-per-line protocol.
It keeps one quiet Singular subprocess alive and sends it a fresh polynomial
command for each request, so benchmark iterations do not include Singular
startup. Integer inputs are interpreted in ``Q[x_1, ..., x_n]``, matching
Singular's canonical GCD normalization; rational inputs use the same ring.
The supported operations cover the GCD, exact-division, and squarefree
surfaces required by ``HexMvGcd``'s Phase-4 family matrix.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from typing import TextIO


def _nonunit_multiplicities(encoded: str) -> list[int]:
    """Decode `factorize`'s vector, omitting its coefficient-unit slot."""
    if not encoded:
        return []
    multiplicities = [int(value.strip()) for value in encoded.split(",")]
    return sorted(multiplicities[1:])


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


def _rational_terms(
    encoded: object, nvars: int, label: str
) -> list[tuple[tuple[int, ...], tuple[int, int]]]:
    if not isinstance(encoded, list):
        raise ValueError(f"{label} terms must be a list")
    out: list[tuple[tuple[int, ...], tuple[int, int]]] = []
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
        if not isinstance(coefficient, list) or len(coefficient) != 2:
            raise ValueError(
                f"{label} term {index} coefficient must be [numerator, denominator]"
            )
        numerator, denominator = coefficient
        if any(not isinstance(value, int) or isinstance(value, bool)
               for value in (numerator, denominator)):
            raise ValueError(f"{label} term {index} has a non-integer rational part")
        if denominator == 0:
            raise ValueError(f"{label} term {index} denominator is zero")
        if denominator < 0:
            numerator, denominator = -numerator, -denominator
        key = tuple(exponents)
        if key in seen:
            raise ValueError(f"{label} repeats exponent vector {key}")
        seen.add(key)
        if numerator != 0:
            out.append((key, (numerator, denominator)))
    return out


def _rational_poly_expr(
    terms: list[tuple[tuple[int, ...], tuple[int, int]]]
) -> str:
    if not terms:
        return "0"
    pieces: list[str] = []
    for exponents, (numerator, denominator) in terms:
        factors = [
            f"x{index}" if exponent == 1 else f"x{index}^{exponent}"
            for index, exponent in enumerate(exponents, start=1)
            if exponent > 0
        ]
        monomial = "*".join(factors)
        magnitude = abs(numerator)
        scalar = str(magnitude) if denominator == 1 else f"({magnitude}/{denominator})"
        if not monomial:
            body = scalar
        elif magnitude == denominator:
            body = monomial
        else:
            body = f"{scalar}*{monomial}"
        if not pieces:
            pieces.append(body if numerator > 0 else f"-{body}")
        else:
            pieces.append(("+" if numerator > 0 else "-") + body)
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
        if self._nvars != nvars:
            variables = ",".join(f"x{index}" for index in range(1, nvars + 1))
            self._serial += 1
            ring_name = f"hex_ring_{self._serial}"
            sentinel = f"__HEX_SINGULAR_RING_{self._serial}_READY__"
            self._request(
                f'ring {ring_name}=0,({variables}),lp; print("{sentinel}");',
                sentinel,
            )
            self._nvars = nvars

    def overhead(self) -> None:
        self._serial += 1
        sentinel = f"__HEX_SINGULAR_OVERHEAD_{self._serial}__"
        self._request(f'print("{sentinel}");', sentinel)

    def gcd_is_one(self, nvars: int, left: str, right: str) -> bool:
        return self.gcd_equals(nvars, left, right, "1")

    def gcd_equals(self, nvars: int, left: str, right: str, expected: str) -> bool:
        self._ensure_ring(nvars)
        self._serial += 1
        yes = f"__HEX_SINGULAR_GCD_{self._serial}_YES__"
        no = f"__HEX_SINGULAR_GCD_{self._serial}_NO__"
        command = (
            f"poly hex_left={left}; poly hex_right={right}; "
            f"poly hex_expected={expected}; "
            "poly hex_gcd=gcd(hex_left,hex_right); "
            f'if (hex_gcd==hex_expected) {{ print("{yes}"); }} '
            f'else {{ print("{no}"); }} '
            "kill hex_left; kill hex_right; kill hex_expected; kill hex_gcd;"
        )
        return self._read_bool(command, yes, no, "GCD")

    def div_equals(
        self, nvars: int, dividend: str, divisor: str, expected: str
    ) -> bool:
        self._ensure_ring(nvars)
        self._serial += 1
        yes = f"__HEX_SINGULAR_DIV_{self._serial}_YES__"
        no = f"__HEX_SINGULAR_DIV_{self._serial}_NO__"
        command = (
            f"poly hex_dividend={dividend}; poly hex_divisor={divisor}; "
            f"poly hex_expected={expected}; "
            "poly hex_quotient=hex_dividend/hex_divisor; "
            f'if (hex_quotient==hex_expected && '
            f'hex_quotient*hex_divisor==hex_dividend) {{ print("{yes}"); }} '
            f'else {{ print("{no}"); }} '
            "kill hex_dividend; kill hex_divisor; kill hex_expected; "
            "kill hex_quotient;"
        )
        return self._read_bool(command, yes, no, "division")

    def squarefree_multiplicities(self, nvars: int, polynomial: str) -> list[int]:
        self._ensure_ring(nvars)
        self._serial += 1
        prefix = f"__HEX_SINGULAR_SQF_{self._serial}__"
        command = (
            f"poly hex_input={polynomial}; list hex_factors=factorize(hex_input); "
            "intvec hex_multiplicities=hex_factors[2]; "
            f'print("{prefix}"+string(hex_multiplicities)); '
            "kill hex_input; kill hex_factors; kill hex_multiplicities;"
        )
        self._stdin.write(command + "\n")
        self._stdin.flush()
        for line in self._stdout:
            answer = line.rstrip("\n").strip()
            if answer.startswith(prefix):
                encoded = answer[len(prefix):].strip()
                return _nonunit_multiplicities(encoded)
        raise RuntimeError("Singular closed stdout before the squarefree response")

    def _read_bool(self, command: str, yes: str, no: str, label: str) -> bool:
        self._stdin.write(command + "\n")
        self._stdin.flush()
        for line in self._stdout:
            answer = line.rstrip("\n")
            if answer == yes:
                return True
            if answer == no:
                return False
        raise RuntimeError(f"Singular closed stdout before the {label} response sentinel")


def _dispatch(request: dict[str, object], session: SingularSession) -> bool | list[int]:
    family = request.get("family")
    if family not in {"integer_mpoly", "rational_mpoly"}:
        raise ValueError(f"unknown Singular family: {request.get('family')!r}")
    operation = request.get("op")
    if operation == "overhead":
        session.overhead()
        return True
    if operation not in {"gcd_is_one", "gcd_equals", "div_equals", "squarefree"}:
        raise ValueError(f"unknown Singular integer_mpoly operation: {operation!r}")
    nvars = request.get("nvars")
    if not isinstance(nvars, int) or isinstance(nvars, bool) or nvars <= 0:
        raise ValueError("nvars must be a positive integer")
    parse = _terms if family == "integer_mpoly" else _rational_terms
    render = _poly_expr if family == "integer_mpoly" else _rational_poly_expr
    left = render(parse(request.get("a"), nvars, "a"))
    if operation == "squarefree":
        return session.squarefree_multiplicities(nvars, left)
    right = render(parse(request.get("b"), nvars, "b"))
    if operation == "gcd_is_one":
        if not session.gcd_is_one(nvars, left, right):
            raise ValueError("Singular computed a nonunit GCD for the coprime fixture")
        return True
    expected = render(parse(request.get("expected"), nvars, "expected"))
    if operation == "gcd_equals" and not session.gcd_equals(
        nvars, left, right, expected
    ):
        raise ValueError("Singular GCD differs from the expected canonical polynomial")
    if operation == "div_equals" and not session.div_equals(
        nvars, left, right, expected
    ):
        raise ValueError("Singular exact quotient differs from the expected polynomial")
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
