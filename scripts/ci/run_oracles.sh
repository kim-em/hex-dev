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
#
# HEX_LIBRARY_FILTER is an optional whitespace-separated list of libraries.
# Empty or unset means all libraries. `--list` prints the tuple registry without
# building or checking oracle dependencies for use by the CI classifier.

set -uo pipefail

work_dir="$(mktemp -d "${TMPDIR:-/tmp}/hex-oracles.XXXXXX")"
trap 'rm -rf -- "$work_dir"' EXIT

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
  "HexRealAlgebraic|hexrealalgebraic_emit_fixtures|scripts/oracle/real_algebraic_flint.py|conformance-fixtures/HexRealAlgebraic/real_algebraic.jsonl"
  # SymPy backed
  "HexDeterminant|hexdeterminant_emit_carrier_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexDeterminant/carriers.jsonl"
  "HexRationalFn|hexrationalfn_emit_fixtures|scripts/oracle/rationalfn_sympy.py|conformance-fixtures/HexRationalFn/rationalfn.jsonl"
  "HexMvPoly|hexmvpoly_emit_fixtures|scripts/oracle/mvpoly_sympy.py|conformance-fixtures/HexMvPoly/mvpoly.jsonl"
  "HexDeterminantalIdeal|hexdeterminantalideal_emit_fixtures|scripts/oracle/detideal_sympy.py|conformance-fixtures/HexDeterminantalIdeal/detideal.jsonl"
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
  # Exact Python integer/Fraction Cartesian enumeration
  "HexLatticeEnum|hexlatticeenum_emit_fixtures|scripts/oracle/lattice_enum.py|conformance-fixtures/HexLatticeEnum/latticeenum.jsonl"
  # Conway tables backed
  "HexConway|hexconway_emit_fixtures|scripts/oracle/conway_luebeck.py|conformance-fixtures/HexConway/conway.jsonl"
  # pinned external nauty 2.9.3 backed (vendored source, project shim)
  "HexGraphIso|hexgraphiso_emit_fixtures|scripts/oracle/graphiso_nauty.py|conformance-fixtures/HexGraphIso/graphiso.jsonl"
  # GAP 4.x, required for permutation-group conformance
  "HexPermGroup|hexpermgroup_emit_fixtures|scripts/oracle/perm_group_gap.py|conformance-fixtures/HexPermGroup/permgroup.jsonl"
)

if [ "${1:-}" = "--list" ]; then
  printf '%s\n' "${ORACLES[@]}"
  exit 0
fi

library_selected() {
  local wanted="$1"
  [ -z "${HEX_LIBRARY_FILTER:-}" ] || [[ " $HEX_LIBRARY_FILTER " == *" $wanted "* ]]
}

if [ -z "${HEX_LIBRARY_FILTER:-}" ]; then
  echo "Oracle library filter: all libraries (no filter)"
else
  echo "Oracle library filter: $HEX_LIBRARY_FILTER"
fi

# Local development may intentionally run only the installed comparators, but
# release CI must never turn a missing oracle dependency into a green `SKIP`.
# Preflight the required oracle dependency families before emitting any fixtures so a
# broken installation fails early and unambiguously.
if [ "${HEX_REQUIRE_ORACLES:-0}" = "1" ]; then
  if ! command -v gap >/dev/null 2>&1; then
    echo "FAIL: required GAP oracle is unavailable" >&2
    exit 1
  fi
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
  if ! python3 scripts/oracle/real_algebraic_flint.py --preflight --require-oracles; then
    echo "FAIL: required real-algebraic oracle capabilities are unavailable" >&2
    exit 1
  fi
fi

FILTERED_ORACLES=()
for entry in "${ORACLES[@]}"; do
  IFS='|' read -r lib _ _ _ <<<"$entry"
  if library_selected "$lib"; then
    FILTERED_ORACLES+=("$entry")
  fi
done

failed=0

# One combined build of every emit executable: parallel `lake exe`
# invocations would contend on the Lake build lock, and one build
# parallelizes internally anyway.
emits=()
for entry in "${FILTERED_ORACLES[@]}"; do
  IFS='|' read -r _ emit _ _ <<<"$entry"
  emits+=("$emit")
done
if [ "${#emits[@]}" -gt 0 ] && ! lake build "${emits[@]}"; then
  echo "FAIL: building emit executables" >&2
  exit 1
fi

run_tuple() {
  local entry="$1"
  local index="$2"
  local lib emit oracle fixture
  IFS='|' read -r lib emit oracle fixture <<<"$entry"
  local fresh="$work_dir/${lib}-${index}-fresh.jsonl"

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

  if [ "$lib" = "HexRealAlgebraic" ]; then
    local repr_fresh="$work_dir/HexRealAlgebraic-ReprChecks.lean"
    if ! ".lake/build/bin/$emit" --repr >"$repr_fresh" ||
        ! diff -u conformance/HexRealAlgebraic/ReprChecks.lean "$repr_fresh"; then
      echo "FAIL: $lib :: generated Lean Repr checks differ from the compiled fixture"
      return 1
    fi
    if ! python3 -m unittest scripts.oracle.test_real_algebraic_flint; then
      echo "FAIL: $lib :: oracle rejection tests failed"
      return 1
    fi
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
}

run_one() {
  local entry="$1"
  local index="$2"
  local lib emit _oracle _fixture
  IFS='|' read -r lib emit _oracle _fixture <<<"$entry"
  local log="$work_dir/oracle-${index}.log"
  local start end elapsed rc
  start=$(date +%s)
  if run_tuple "$entry" "$index" >"$log" 2>&1; then rc=0; else rc=$?; fi
  end=$(date +%s)
  elapsed=$((end - start))
  printf 'TIMING: %s (%s) %ss\n' "$lib" "$emit" "$elapsed" >>"$log"
  return "$rc"
}

jobs="${HEX_ORACLE_JOBS:-$(nproc)}"
running=0
declare -A index_of_pid status_of
reap() {
  local done_pid st
  if wait -n -p done_pid; then st=0; else st=$?; fi
  status_of["${index_of_pid[$done_pid]}"]=$st
  running=$((running - 1))
}
for index in "${!FILTERED_ORACLES[@]}"; do
  entry="${FILTERED_ORACLES[$index]}"
  run_one "$entry" "$index" &
  index_of_pid[$!]="$index"
  running=$((running + 1))
  if [ "$running" -ge "$jobs" ]; then
    reap
  fi
done
while [ "$running" -gt 0 ]; do
  reap
done
for index in "${!FILTERED_ORACLES[@]}"; do
  if [ "${status_of[$index]:-1}" -ne 0 ]; then
    failed=1
  fi
  cat "$work_dir/oracle-${index}.log"
done

if [ "$failed" -ne 0 ]; then
  echo
  echo "Conformance: oracle run failed; see preceding markers for the libraries." >&2
  exit 1
fi

# Exercise the independent Lean/native binding in process against the same
# committed corpus. The executable is built by the shared build phase above;
# this adds only the FFI calls (about 0.1 s locally), not another elaboration.
if library_selected HexGraphIso && ! .lake/packages/NautyFFI/.lake/build/bin/nautyffi_tests; then
  echo "Conformance: in-process nauty-ffi fixture check failed." >&2
  exit 1
fi

echo
echo "Conformance: all oracles passed."
