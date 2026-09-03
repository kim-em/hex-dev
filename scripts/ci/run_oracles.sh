#!/usr/bin/env bash
# Parallel oracle runner used by `.github/workflows/ci.yml`.
#
# Replaces the per-oracle matrix that previously fanned out into 11
# ubuntu jobs. All oracle dependencies (FLINT, PARI, SymPy, Conway
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
# Oracles are independent, so they run through a worker pool
# (HEX_ORACLE_JOBS, default nproc) after one combined `lake build` of
# every emit executable; per-library output is captured and printed in
# tuple order. Exits non-zero if any library failed, with a clear
# marker per failing library. Same-runner process parallelism is the
# form SPEC/CI.md permits: it raises no runner count.

set -uo pipefail

# Local development may intentionally run only the installed comparators, but
# release CI must never turn a missing oracle dependency into a green `SKIP`.
# Preflight the required oracle dependency families before emitting any fixtures so a
# broken installation fails early and unambiguously.
if [ "${HEX_REQUIRE_ORACLES:-0}" = "1" ]; then
  if ! python3 - <<'PY'
import flint
import cypari2
import conway_polynomials
import sympy
PY
  then
    echo "FAIL: required oracle dependencies are unavailable" >&2
    exit 1
  fi
fi

# Tuples are encoded as `lib|emit_exe|oracle_script|fixture_path`.
ORACLES=(
  # python-flint backed
  "HexPoly|hexpoly_emit_fixtures|scripts/oracle/poly_flint.py|conformance-fixtures/HexPoly/poly.jsonl"
  "HexPolyFast|hexpolyfast_emit_fixtures|scripts/oracle/polyfast_flint.py|conformance-fixtures/HexPolyFast/polyfast.jsonl"
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
  "HexHermite|hexhermite_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexHermite/hermite.jsonl"
  "HexSmith|hexsmith_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexSmith/smith.jsonl"
  "HexCharPoly|hexcharpoly_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexCharPoly/charpoly.jsonl"
  "HexMinPoly|hexminpoly_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexMinPoly/minpoly.jsonl"
  "HexGramSchmidt|hexgramschmidt_emit_fixtures|scripts/oracle/gs_flint.py|conformance-fixtures/HexGramSchmidt/gram_schmidt.jsonl"
  "HexRealRoots|hexrealroots_emit_fixtures|scripts/oracle/realroots_flint.py|conformance-fixtures/HexRealRoots/realroots.jsonl"
  "HexRCF|hexrcf_emit_fixtures|scripts/oracle/rcf_flint.py|conformance-fixtures/HexRCF/rcf.jsonl"
  "HexRoots|hexroots_emit_fixtures|scripts/oracle/roots_flint.py|conformance-fixtures/HexRoots/roots.jsonl"
  # SymPy backed
  "HexMvPoly|hexmvpoly_emit_fixtures|scripts/oracle/mvpoly_sympy.py|conformance-fixtures/HexMvPoly/mvpoly.jsonl"
  "HexTruncatedSeries|hextruncatedseries_emit_fixtures|scripts/oracle/series_sympy.py|conformance-fixtures/HexTruncatedSeries/series.jsonl"
  "HexSparsePoly|hexsparsepoly_emit_fixtures|scripts/oracle/sparsepoly_sympy.py|conformance-fixtures/HexSparsePoly/sparsepoly.jsonl"
  "HexModular|hexmodular_emit_fixtures|scripts/oracle/modular_sympy.py|conformance-fixtures/HexModular/modular.jsonl"
  "HexPolyZGcd|hexpolyzgcd_emit_fixtures|scripts/oracle/zgcd_sympy.py|conformance-fixtures/HexPolyZGcd/zgcd.jsonl"
  "HexMvGcd|hexmvgcd_emit_fixtures|scripts/oracle/mvgcd_sympy.py|conformance-fixtures/HexMvGcd/mvgcd.jsonl"
  "HexMvHensel|hexmvhensel_emit_fixtures|scripts/oracle/mvhensel_sympy.py|conformance-fixtures/HexMvHensel/mvhensel.jsonl"
  "HexMvFactor|hexmvfactor_emit_fixtures|scripts/oracle/mvfactor_sympy.py|conformance-fixtures/HexMvFactor/mvfactor.jsonl"
  "HexPolySmith|hexpolysmith_emit_fixtures|scripts/oracle/polymatrix.py|conformance-fixtures/HexPolySmith/smith.jsonl"
  # python-flint + PARI backed
  "HexResultant|hexresultant_emit_fixtures|scripts/oracle/resultant_flint_pari.py|conformance-fixtures/HexResultant/resultant.jsonl"
  # PARI backed
  "HexHensel|hexhensel_emit_fixtures|scripts/oracle/hensel_pari.py|conformance-fixtures/HexHensel/hensel.jsonl"
  "HexPrimality|hexprimality_emit_fixtures|scripts/oracle/primality_pari.py|conformance-fixtures/HexPrimality/primality.jsonl"
  "HexIntFactor|hexintfactor_emit_fixtures|scripts/oracle/intfactor_pari.py|conformance-fixtures/HexIntFactor/intfactor.jsonl"
  "HexNumberField|hexnumberfield_emit_fixtures|scripts/oracle/number_field_flint_pari.py|conformance-fixtures/HexNumberField/number_field.jsonl"
  "HexNumberFieldTower|hexnumberfieldtower_emit_fixtures|scripts/oracle/number_field_tower_pari.py|conformance-fixtures/HexNumberFieldTower/number_field_tower.jsonl"
  # Conway tables backed
  "HexConway|hexconway_emit_fixtures|scripts/oracle/conway_luebeck.py|conformance-fixtures/HexConway/conway.jsonl"
  # pinned external nauty 2.9.3 backed (vendored source, project shim)
  "HexGraphIso|hexgraphiso_emit_fixtures|scripts/oracle/graphiso_nauty.py|conformance-fixtures/HexGraphIso/graphiso.jsonl"
)

failed=0

# One combined build of every emit executable: parallel `lake exe`
# invocations would contend on the Lake build lock, and one build
# parallelizes internally anyway.
emits=()
for entry in "${ORACLES[@]}"; do
  IFS='|' read -r _ emit _ _ <<<"$entry"
  emits+=("$emit")
done
if ! lake build "${emits[@]}"; then
  echo "FAIL: building emit executables" >&2
  exit 1
fi

run_one() {
  local entry="$1"
  local lib emit oracle fixture
  IFS='|' read -r lib emit oracle fixture <<<"$entry"
  local fresh="/tmp/${lib}-fresh.jsonl"
  local log="/tmp/oracle-${lib}.log"
  {
    echo
    echo "=========================================================="
    echo ">>> $lib :: emit=$emit oracle=$oracle"
    echo "=========================================================="

    if ! ".lake/build/bin/$emit" >"$fresh"; then
      echo "FAIL: $lib :: $emit exited non-zero"
      return 1
    fi

    if ! diff -u "$fixture" "$fresh"; then
      echo "FAIL: $lib :: fresh emission diverges from committed fixture"
      return 1
    fi

    local oracle_args=()
    case "$oracle" in
      *primality_pari.py)
        if [ "${HEX_REQUIRE_ORACLES:-0}" = "1" ]; then
          oracle_args=(--require-oracles)
        fi
        ;;
      *conway_luebeck.py)
        if [ "${HEX_REQUIRE_ORACLES:-0}" = "1" ]; then
          oracle_args=(--require-conway-polynomials)
        else
          # The committed Lübeck cache is always checked. Locally, add the
          # package-backed leg when available and report a clean SKIP otherwise.
          oracle_args=(--check-conway-polynomials)
        fi
        ;;
    esac

    if ! python3 "$oracle" "${oracle_args[@]}" <"$fresh"; then
      echo "FAIL: $lib :: oracle $oracle reported a divergence"
      return 1
    fi

    echo "OK: $lib"
  } >"$log" 2>&1
}

jobs="${HEX_ORACLE_JOBS:-$(nproc)}"
running=0
declare -A lib_of_pid status_of
reap() {
  local done_pid st
  if wait -n -p done_pid; then st=0; else st=$?; fi
  status_of["${lib_of_pid[$done_pid]}"]=$st
  running=$((running - 1))
}
for entry in "${ORACLES[@]}"; do
  IFS='|' read -r lib _ _ _ <<<"$entry"
  run_one "$entry" &
  lib_of_pid[$!]="$lib"
  running=$((running + 1))
  if [ "$running" -ge "$jobs" ]; then
    reap
  fi
done
while [ "$running" -gt 0 ]; do
  reap
done
for entry in "${ORACLES[@]}"; do
  IFS='|' read -r lib _ _ _ <<<"$entry"
  if [ "${status_of[$lib]:-1}" -ne 0 ]; then
    failed=1
  fi
  cat "/tmp/oracle-${lib}.log"
done

if [ "$failed" -ne 0 ]; then
  echo
  echo "Conformance: oracle run failed; see preceding markers for the libraries." >&2
  exit 1
fi

# Exercise the independent Lean/native binding in process against the same
# committed corpus. The executable is built by the shared build phase above;
# this adds only the FFI calls (about 0.1 s locally), not another elaboration.
if ! .lake/packages/NautyFFI/.lake/build/bin/nautyffi_tests; then
  echo "Conformance: in-process nauty-ffi fixture check failed." >&2
  exit 1
fi

echo
echo "Conformance: all oracles passed."
