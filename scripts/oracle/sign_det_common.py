"""Serialization checks shared by independent exact sign/root oracles.

This module contains no polynomial arithmetic or expected-root computation.
"""
from typing import Any

from scripts.oracle.common import OracleMismatch


def require(condition: bool, message: str) -> None:
    if not condition:
        raise OracleMismatch(message)


def check_output(output: Any, expected: list[dict[str, Any]] | None, arity: int) -> None:
    require(isinstance(output, dict), "missing constructor result")
    if expected is None:
        require(output == {"status": "invalid-domain"}, "invalid domain was accepted")
        return
    require(output.get("status") == "ok", f"valid-domain construction failed: {output!r}")
    require(output.get("replay") is True, "produced replay did not pass its checker")
    check_table(output.get("table"), expected, arity)


def check_table(table: Any, expected: list[dict[str, Any]], arity: int) -> None:
    require(isinstance(table, list), "missing sparse sign table")
    seen = set()
    for row in table:
        require(isinstance(row, dict) and set(row) == {"signs", "count"}, "malformed table row")
        signs, count = row["signs"], row["count"]
        require(isinstance(signs, list) and len(signs) == arity and
                all(type(s) is int and s in (-1, 0, 1) for s in signs), "malformed sign condition")
        require(type(count) is int and count > 0, "sparse counts must be positive integers")
        key = tuple(signs)
        require(key not in seen, "duplicate sign condition")
        seen.add(key)
    require(table == sorted(table, key=lambda row: row["signs"]),
            "produced table rows are not in the serialization order")
    require(table == expected, f"complete sign table differs: Lean={table!r}, oracle={expected!r}")


def sign_vector(value: Any, size: int) -> bool:
    return (isinstance(value, list) and len(value) == size and
            all(type(v) is int and v in (-1, 0, 1) for v in value))


def check_encoding(value: Any, degree: int) -> None:
    require(isinstance(value, dict) and isinstance(value.get("indices"), list) and
            all(type(i) is int for i in value["indices"]) and
            value["indices"] == list(range(1, degree + 1)) and
            sign_vector(value.get("signs"), degree) and value.get("replay") is True,
            "malformed or unchecked full root encoding")
