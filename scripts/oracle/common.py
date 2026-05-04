"""Shared utilities for Hex conformance oracles.

Defines the JSONL fixture schemas, the JSON failure-record schema, and
helpers for reading Lean-emitted records, comparing oracle outputs to
the Lean values, and writing replayable failure records on mismatch.

Stdlib only.  Oracle drivers under ``scripts/oracle/`` add the
external-tool import (e.g. ``flint`` from ``python-flint``).

JSONL fixture record shape (one record per line):

* ``poly``       — ``{"kind": "poly",       "lib": str, "case": str,
                      "coeffs": [int...], "modulus": int|null}``
* ``matrix``     — ``{"kind": "matrix",     "lib": str, "case": str,
                      "rows": [[int...]...]}``
* ``lattice``    — ``{"kind": "lattice",    "lib": str, "case": str,
                      "basis": [[int...]...]}``
* ``prime``      — ``{"kind": "prime",      "lib": str, "case": str,
                      "p": int, "n": int}``
* ``gfq_bridge`` — ``{"kind": "gfq_bridge", "lib": str, "case": str,
                      "p": int, "modulus": [int...],
                      "a": [int...], "b": [int...]}``
                     (two reduced operands `a` and `b` over `F_p[x] /
                      (modulus)`; carries the inputs both Lean
                      representations consume so the oracle can verify
                      packed and generic answers independently.)
* ``gfqfield``   — ``{"kind": "gfqfield",   "lib": str, "case": str,
                      "p": int, "modulus": [int...],
                      "a": [int...], "b": [int...], "zexp": int}``
                     (a, b are reduced operands modulo `m(x)`; `zexp`
                      is the integer exponent for the `zpow` op.  `b`
                      must be nonzero so that `a / b` is well-defined.)

Result records (emitted by Lean alongside the fixture, on the same
JSONL stream) carry the operation name and Lean's computed answer:

* ``{"kind": "result", "lib": str, "case": str, "op": str,
     "value": <op-specific JSON>}``

The ``op`` strings are oracle-defined; e.g. ``poly_flint.py`` knows
``mul`` (value is the coefficient list of the product), ``gcd``
(coefficient list of the monic gcd), ``divmod`` (a ``[quot, rem]``
pair of coefficient lists).

JSON failure record shape (one file per failure, written to a
caller-supplied directory):

``{"library": str, "profile": "ci"|"local", "seed": int,
   "case_id": str, "kind": str, "input": <case object>,
   "lean_output": <serialised>, "oracle_output": <serialised>,
   "oracle_name": str, "oracle_version": str, "diff": str}``
"""
from __future__ import annotations

import json
import os
import sys
from pathlib import Path
from typing import Any, Iterable, Iterator


VALID_FIXTURE_KINDS = frozenset(
    {"poly", "matrix", "lattice", "prime", "gfq_bridge", "gfqfield"}
)


class FixtureError(ValueError):
    """Raised when a JSONL record fails schema validation."""


class OracleMismatch(AssertionError):
    """Raised when an oracle output does not match the Lean output.

    Carries enough context that the failure record was written before
    re-raising; the oracle CLI converts this into a non-zero exit.
    """


def _validate_fixture(record: dict[str, Any]) -> None:
    kind = record.get("kind")
    if kind not in VALID_FIXTURE_KINDS and kind != "result":
        raise FixtureError(f"unknown fixture kind: {kind!r}")
    for key in ("lib", "case"):
        if not isinstance(record.get(key), str):
            raise FixtureError(f"missing/invalid {key!r} in {record!r}")
    if kind == "poly":
        coeffs = record.get("coeffs")
        if not isinstance(coeffs, list) or not all(isinstance(c, int) for c in coeffs):
            raise FixtureError(f"poly.coeffs must be List[int]: {record!r}")
        modulus = record.get("modulus", None)
        if modulus is not None and not isinstance(modulus, int):
            raise FixtureError(f"poly.modulus must be int or null: {record!r}")
    elif kind == "matrix":
        rows = record.get("rows")
        if not isinstance(rows, list) or not all(
            isinstance(row, list) and all(isinstance(x, int) for x in row)
            for row in rows
        ):
            raise FixtureError(f"matrix.rows must be List[List[int]]: {record!r}")
    elif kind == "lattice":
        basis = record.get("basis")
        if not isinstance(basis, list) or not all(
            isinstance(row, list) and all(isinstance(x, int) for x in row)
            for row in basis
        ):
            raise FixtureError(f"lattice.basis must be List[List[int]]: {record!r}")
    elif kind == "prime":
        for key in ("p", "n"):
            if not isinstance(record.get(key), int):
                raise FixtureError(f"prime.{key} must be int: {record!r}")
    elif kind == "gfq_bridge":
        if not isinstance(record.get("p"), int):
            raise FixtureError(f"gfq_bridge.p must be int: {record!r}")
        for key in ("modulus", "a", "b"):
            value = record.get(key)
            if not isinstance(value, list) or not all(isinstance(c, int) for c in value):
                raise FixtureError(
                    f"gfq_bridge.{key} must be List[int]: {record!r}"
                )
    elif kind == "gfqfield":
        if not isinstance(record.get("p"), int):
            raise FixtureError(f"gfqfield.p must be int: {record!r}")
        if not isinstance(record.get("zexp"), int):
            raise FixtureError(f"gfqfield.zexp must be int: {record!r}")
        for key in ("modulus", "a", "b"):
            seq = record.get(key)
            if not isinstance(seq, list) or not all(isinstance(x, int) for x in seq):
                raise FixtureError(
                    f"gfqfield.{key} must be List[int]: {record!r}"
                )
    elif kind == "result":
        if not isinstance(record.get("op"), str):
            raise FixtureError(f"result.op must be str: {record!r}")
        if "value" not in record:
            raise FixtureError(f"result.value missing: {record!r}")


def read_fixtures(source: str | Path | None = None) -> Iterator[dict[str, Any]]:
    """Yield validated JSONL records from ``source`` (path) or stdin.

    Blank lines and ``#``-prefixed comment lines are ignored so that
    the JSONL files stay diffable with optional human annotations.
    """
    if source is None:
        stream: Iterable[str] = sys.stdin
        close = False
    else:
        path = Path(source)
        stream = path.open("r", encoding="utf-8")
        close = True
    try:
        for lineno, raw in enumerate(stream, 1):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise FixtureError(
                    f"{source or '<stdin>'}:{lineno}: invalid JSON ({exc})"
                ) from exc
            if not isinstance(record, dict):
                raise FixtureError(
                    f"{source or '<stdin>'}:{lineno}: expected JSON object"
                )
            _validate_fixture(record)
            yield record
    finally:
        if close:
            stream.close()  # type: ignore[union-attr]


def split_fixtures_results(
    records: Iterable[dict[str, Any]],
) -> tuple[dict[tuple[str, str], dict[str, Any]], list[dict[str, Any]]]:
    """Partition a JSONL stream into ``(cases_by_id, results)``.

    The ``cases_by_id`` map is keyed by ``(lib, case)`` so a result
    record can recover its input.  ``results`` preserves stream order
    so the oracle reports failures in the order Lean emitted them.
    """
    cases: dict[tuple[str, str], dict[str, Any]] = {}
    results: list[dict[str, Any]] = []
    for record in records:
        if record["kind"] == "result":
            results.append(record)
        else:
            cases[(record["lib"], record["case"])] = record
    return cases, results


def write_failure(
    failure_dir: str | Path,
    *,
    library: str,
    profile: str,
    seed: int,
    case_id: str,
    kind: str,
    input_record: dict[str, Any],
    lean_output: Any,
    oracle_output: Any,
    oracle_name: str,
    oracle_version: str,
    diff: str,
) -> Path:
    """Write a JSON failure record and return its path.

    The filename is ``<library>-<seed>-<case_id>.json`` so concurrent
    oracle runs against different libraries / seeds don't collide.
    """
    out_dir = Path(failure_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    record = {
        "library": library,
        "profile": profile,
        "seed": seed,
        "case_id": case_id,
        "kind": kind,
        "input": input_record,
        "lean_output": lean_output,
        "oracle_output": oracle_output,
        "oracle_name": oracle_name,
        "oracle_version": oracle_version,
        "diff": diff,
    }
    safe_case = case_id.replace("/", "_")
    out_path = out_dir / f"{library}-{seed}-{safe_case}.json"
    out_path.write_text(json.dumps(record, indent=2, sort_keys=True), encoding="utf-8")
    return out_path


def assert_equal(
    lean: Any,
    oracle: Any,
    *,
    library: str,
    case_id: str,
    kind: str,
    input_record: dict[str, Any],
    oracle_name: str,
    oracle_version: str,
    failure_dir: str | Path | None = None,
    profile: str = "ci",
    seed: int = 0,
) -> None:
    """Assert ``lean == oracle``; on mismatch write a failure record then raise.

    ``failure_dir`` defaults to the ``HEX_FAILURE_DIR`` environment
    variable, then to ``conformance-failures`` under the current
    working directory.
    """
    if lean == oracle:
        return
    target = (
        failure_dir
        if failure_dir is not None
        else os.environ.get("HEX_FAILURE_DIR", "conformance-failures")
    )
    diff = f"lean={lean!r} oracle={oracle!r}"
    path = write_failure(
        target,
        library=library,
        profile=profile,
        seed=seed,
        case_id=case_id,
        kind=kind,
        input_record=input_record,
        lean_output=lean,
        oracle_output=oracle,
        oracle_name=oracle_name,
        oracle_version=oracle_version,
        diff=diff,
    )
    raise OracleMismatch(
        f"{library}/{case_id} ({kind}): Lean and {oracle_name} disagree.\n"
        f"  diff: {diff}\n"
        f"  failure record: {path}"
    )
