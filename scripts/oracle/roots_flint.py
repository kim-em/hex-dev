#!/usr/bin/env python3
"""python-flint oracle driver for `hex-roots`.

Reads a JSONL stream produced by `lake exe hexroots_emit_fixtures` (or
the committed sample at `conformance-fixtures/HexRoots/roots.jsonl`)
and cross-checks each `isolateAll32` result against python-flint's
`fmpz_poly.complex_roots()` (certified Arb balls with multiplicities).
On mismatch, writes a JSON failure record under `conformance-failures/`
and exits non-zero so CI fails the job.

Usage::

    # CI: pipe Lean's emission directly into the oracle.
    lake exe hexroots_emit_fixtures | python3 scripts/oracle/roots_flint.py

    # Local: replay against the committed sample.
    python3 scripts/oracle/roots_flint.py --check

    # Read from an explicit JSONL path.
    python3 scripts/oracle/roots_flint.py path/to/file.jsonl

Each `isolateAll32` result value is a JSON array of certification discs,
one object per result, carrying `kind` (`"atom"` | `"cluster"`), `k`
(root count with multiplicity, `1` for atoms), the disc centre as an
exact rational (`re_num` / `re_den` / `im_num` / `im_den`), and `prec`
(the stored square's precision, so the circumscribed-disc radius is
`sqrt(2) * 2^{-prec}`).  A `"none"` value records a driver give-up and
is a hard failure here.

For each polynomial the oracle checks, using rigorous `arb`/`acb`
comparisons at high working precision:

* the sum of Lean `k` values equals the polynomial's degree and equals
  the sum of flint root multiplicities;
* every flint root ball lies inside exactly one Lean disc, where
  "inside" is the rigorous ball-containment `|root - c| <= sqrt(2) *
  2^{-prec}` (the flint ball radius is subsumed by `arb` arithmetic on
  ``abs(root - c)``);
* each Lean atom disc (`k == 1`) contains exactly one flint root of
  multiplicity 1, and each Lean cluster disc contains flint roots of
  total multiplicity equal to `k`.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexRoots" / "roots.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

# Working precision (bits) for the rigorous arb/acb containment checks.
# Far finer than the target-32 disc radius, so containment is decisive.
WORK_PREC = 333

# Allow `import scripts.oracle.common` even when the script is invoked
# directly (rather than via `python -m`).
sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    read_fixtures,
    split_fixtures_results,
    write_failure,
)


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]
        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _disc_center(disc: dict[str, Any]):
    """Exact `acb` centre of a Lean disc from its rational components."""
    from flint import acb, fmpq  # type: ignore[import-not-found]
    return acb(
        fmpq(int(disc["re_num"]), int(disc["re_den"])),
        fmpq(int(disc["im_num"]), int(disc["im_den"])),
    )


def _disc_radius(prec: int):
    """Rigorous `arb` circumscribed-disc radius `sqrt(2) * 2^{-prec}`."""
    from flint import arb, fmpq  # type: ignore[import-not-found]
    if prec >= 0:
        scale = fmpq(1, 1 << prec)
    else:
        scale = fmpq(1 << (-prec), 1)
    return arb(2).sqrt() * arb(scale)


def _inside(root, center, radius) -> bool:
    """Rigorous ball containment: the whole flint root ball lies in the
    Lean disc iff ``abs(root - center) <= radius`` as an `arb` relation
    (True only when certainly true)."""
    return bool(abs(root - center) <= radius)


def _fail(
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
    lib: str,
    case_id: str,
    coeffs: list[int],
    lean_value: Any,
    oracle_value: Any,
    oracle_version: str,
    message: str,
):
    path = write_failure(
        failure_dir,
        library=lib,
        profile=profile,
        seed=seed,
        case_id=case_id,
        kind="isolateAll32",
        input_record={"coeffs": coeffs},
        lean_output=lean_value,
        oracle_output=oracle_value,
        oracle_name="python-flint",
        oracle_version=oracle_version,
        diff=message,
    )
    raise OracleMismatch(
        f"{lib}/{case_id} (isolateAll32): {message}\n  failure record: {path}"
    )


def _check_case(
    *,
    lib: str,
    case_id: str,
    coeffs: list[int],
    lean_value: Any,
    failure_dir: Path,
    profile: str,
    seed: int,
    oracle_version: str,
) -> None:
    from flint import ctx, fmpz_poly  # type: ignore[import-not-found]

    ctx.prec = WORK_PREC

    if lean_value == "none":
        _fail(
            failure_dir=failure_dir, profile=profile, seed=seed, lib=lib,
            case_id=case_id, coeffs=coeffs, lean_value=lean_value,
            oracle_value=None, oracle_version=oracle_version,
            message="Lean driver returned none (isolateAll? gave up)",
        )
    if not isinstance(lean_value, list):
        _fail(
            failure_dir=failure_dir, profile=profile, seed=seed, lib=lib,
            case_id=case_id, coeffs=coeffs, lean_value=lean_value,
            oracle_value=None, oracle_version=oracle_version,
            message=f"isolateAll32 value must be a JSON array, got {lean_value!r}",
        )

    p = fmpz_poly(coeffs)
    degree = p.degree()
    roots = p.complex_roots()  # list of (acb, multiplicity)
    total_mult = sum(m for _, m in roots)

    # (a) counts: sum of Lean k == degree == sum of flint multiplicities.
    sum_k = sum(int(d["k"]) for d in lean_value)
    if not (sum_k == degree == total_mult):
        _fail(
            failure_dir=failure_dir, profile=profile, seed=seed, lib=lib,
            case_id=case_id, coeffs=coeffs, lean_value=lean_value,
            oracle_value={"degree": degree, "flint_total_mult": total_mult},
            oracle_version=oracle_version,
            message=(
                f"count mismatch: sum(Lean k)={sum_k}, degree={degree}, "
                f"sum(flint mult)={total_mult}"
            ),
        )

    centers = [_disc_center(d) for d in lean_value]
    radii = [_disc_radius(int(d["prec"])) for d in lean_value]

    # (b) every flint root lies inside exactly one Lean disc, and
    # accumulate per-disc multiplicity totals for (c).
    disc_mult = [0] * len(lean_value)
    disc_count = [0] * len(lean_value)
    for root, mult in roots:
        hits = [i for i in range(len(lean_value))
                if _inside(root, centers[i], radii[i])]
        if len(hits) != 1:
            _fail(
                failure_dir=failure_dir, profile=profile, seed=seed, lib=lib,
                case_id=case_id, coeffs=coeffs, lean_value=lean_value,
                oracle_value={"root": str(root), "containing_discs": hits},
                oracle_version=oracle_version,
                message=(
                    f"flint root {root} lies in {len(hits)} Lean discs "
                    f"(indices {hits}); expected exactly 1"
                ),
            )
        disc_mult[hits[0]] += mult
        disc_count[hits[0]] += 1

    # (c) per-disc multiplicity and atom shape.
    for i, disc in enumerate(lean_value):
        k = int(disc["k"])
        if disc_mult[i] != k:
            _fail(
                failure_dir=failure_dir, profile=profile, seed=seed, lib=lib,
                case_id=case_id, coeffs=coeffs, lean_value=lean_value,
                oracle_value={"disc": i, "flint_mult_in_disc": disc_mult[i]},
                oracle_version=oracle_version,
                message=(
                    f"disc {i} ({disc['kind']}, k={k}) contains flint roots "
                    f"of total multiplicity {disc_mult[i]}"
                ),
            )
        if disc["kind"] == "atom":
            if k != 1 or disc_count[i] != 1:
                _fail(
                    failure_dir=failure_dir, profile=profile, seed=seed,
                    lib=lib, case_id=case_id, coeffs=coeffs,
                    lean_value=lean_value,
                    oracle_value={"disc": i, "flint_roots_in_disc": disc_count[i]},
                    oracle_version=oracle_version,
                    message=(
                        f"atom disc {i} has k={k} and contains {disc_count[i]} "
                        f"flint root(s); expected k=1 with one simple root"
                    ),
                )


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _flint_version()
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        if op != "isolateAll32":
            print(
                f"FAIL {lib}/{case_id}: unsupported op {op!r} in roots_flint.py",
                file=sys.stderr,
            )
            failures += 1
            continue
        poly = cases.get((lib, case_id))
        if poly is None or poly["kind"] != "poly":
            print(
                f"FAIL {lib}/{case_id}: missing paired poly fixture",
                file=sys.stderr,
            )
            failures += 1
            continue
        try:
            _check_case(
                lib=lib,
                case_id=case_id,
                coeffs=list(poly["coeffs"]),
                lean_value=result["value"],
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
                oracle_version=oracle_version,
            )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} (isolateAll32): {exc}", file=sys.stderr)
    print(
        f"roots_flint.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument(
        "input",
        nargs="?",
        help="JSONL fixture path (default: stdin)",
    )
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    if args.check:
        source: str | None = str(DEFAULT_FIXTURE)
    else:
        source = args.input  # may be None → stdin

    try:
        import flint  # noqa: F401  (presence check)
    except ImportError:
        # Mirror the SPEC's `if_available` mode: a missing oracle is a
        # skip, not a failure.  CI invokes `pip install python-flint`
        # before this script, so a failure here in CI means install
        # failed.
        print("SKIP: python-flint not installed", file=sys.stderr)
        return 0

    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
