#!/usr/bin/env bash
# Sequential oracle runner used by `.github/workflows/conformance.yml`.
#
# Replaces the per-oracle matrix that previously fanned out into 11
# ubuntu jobs. All oracle dependencies (FLINT, PARI, fpLLL, Conway
# tables) are installed once at the top of the workflow; this script
# loops over every (lib, emit, oracle, fixture) tuple, cross-checks
# the committed fixture against fresh emission, and pipes the
# emission into the oracle for verification.
#
# Single source of truth for "which library needs which oracle"
# lives below. Adding a new oracle-backed library means appending
# one tuple to ORACLES — do not introduce a new top-level CI job
# (see SPEC/CI.md § Job-count budget).
#
# Exits non-zero on first failing library, with a clear marker
# identifying which library failed.

set -uo pipefail

# Tuples are encoded as `lib|emit_exe|oracle_script|fixture_path`.
ORACLES=(
  # python-flint backed
  "HexPoly|hexpoly_emit_fixtures|scripts/oracle/poly_flint.py|conformance-fixtures/HexPoly/poly.jsonl"
  "HexPolyFp|hexpolyfp_emit_fixtures|scripts/oracle/polyfp_flint.py|conformance-fixtures/HexPolyFp/poly.jsonl"
  "HexBerlekamp|hexberlekamp_emit_fixtures|scripts/oracle/berlekamp_flint.py|conformance-fixtures/HexBerlekamp/berlekamp.jsonl"
  "HexBerlekampZassenhaus|hexbz_emit_fixtures|scripts/oracle/bz_flint.py|conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl"
  "HexPolyZ|hexpolyz_emit_fixtures|scripts/oracle/polyz_flint.py|conformance-fixtures/HexPolyZ/polyz.jsonl"
  "HexGF2|hexgf2_emit_fixtures|scripts/oracle/gf2_flint.py|conformance-fixtures/HexGF2/gf2.jsonl"
  "HexGFq|hexgfq_emit_fixtures|scripts/oracle/gfq_flint.py|conformance-fixtures/HexGFq/gfq.jsonl"
  "HexGFqRing|hexgfqring_emit_fixtures|scripts/oracle/gfqring_flint.py|conformance-fixtures/HexGFqRing/gfqring.jsonl"
  "HexGFqField|hexgfqfield_emit_fixtures|scripts/oracle/gfqfield_flint.py|conformance-fixtures/HexGFqField/gfqfield.jsonl"
  "HexRowReduce|hexrowreduce_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexRowReduce/rowreduce.jsonl"
  "HexDeterminant|hexdeterminant_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexDeterminant/determinant.jsonl"
  "HexBareiss|hexbareiss_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexBareiss/bareiss.jsonl"
  "HexGramSchmidt|hexgramschmidt_emit_fixtures|scripts/oracle/gs_flint.py|conformance-fixtures/HexGramSchmidt/gram_schmidt.jsonl"
  "HexRealRoots|hexrealroots_emit_fixtures|scripts/oracle/realroots_flint.py|conformance-fixtures/HexRealRoots/realroots.jsonl"
  "HexRoots|hexroots_emit_fixtures|scripts/oracle/roots_flint.py|conformance-fixtures/HexRoots/roots.jsonl"
  # PARI backed
  "HexHensel|hexhensel_emit_fixtures|scripts/oracle/hensel_pari.py|conformance-fixtures/HexHensel/hensel.jsonl"
  # Conway tables backed
  "HexConway|hexconway_emit_fixtures|scripts/oracle/conway_luebeck.py|conformance-fixtures/HexConway/conway.jsonl"
)

failed=0
for entry in "${ORACLES[@]}"; do
  IFS='|' read -r lib emit oracle fixture <<<"$entry"

  echo
  echo "=========================================================="
  echo ">>> $lib :: emit=$emit oracle=$oracle"
  echo "=========================================================="

  fresh="/tmp/${lib}-fresh.jsonl"
  if ! lake exe "$emit" >"$fresh"; then
    echo "FAIL: $lib :: lake exe $emit exited non-zero" >&2
    failed=1
    break
  fi

  if ! diff -u "$fixture" "$fresh"; then
    echo "FAIL: $lib :: fresh emission diverges from committed fixture" >&2
    failed=1
    break
  fi

  oracle_args=()
  case "$oracle" in
    *conway_luebeck.py)
      oracle_args=(--require-conway-polynomials)
      ;;
  esac

  if ! python3 "$oracle" "${oracle_args[@]}" <"$fresh"; then
    echo "FAIL: $lib :: oracle $oracle reported a divergence" >&2
    failed=1
    break
  fi

  echo "OK: $lib"
done

if [ "$failed" -ne 0 ]; then
  echo
  echo "Conformance: oracle run failed; see preceding marker for the library." >&2
  exit 1
fi

echo
echo "Conformance: all oracles passed."
