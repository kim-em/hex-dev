#!/usr/bin/env bash
# Parallel oracle runner used by `.github/workflows/ci.yml`.
#
# Replaces the per-oracle matrix that previously fanned out into 11
# ubuntu jobs. All oracle dependencies (FLINT, PARI, SymPy, Conway
# tables) are installed once at the top of the workflow; this script
# loops over every (lib, emit, oracle, fixture) tuple. Fixture emitters
# are compared with their committed output before the oracle runs;
# the compiled-input SQUFOF oracle checks its committed corpus directly.
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
# `--build-only` prepares the selected native targets before parallel CI tails.

set -uo pipefail

mode="${1:-}"
if [ "$#" -gt 1 ] || { [ -n "$mode" ] && [ "$mode" != "--list" ] && [ "$mode" != "--build-only" ]; }; then
  echo "usage: $0 [--list|--build-only]" >&2
  exit 2
fi

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
  "HexModularMatrix|hexmodularmatrix_emit_fixtures|scripts/oracle/modmat_flint.py|conformance-fixtures/HexModularMatrix/modmat.jsonl"
  "HexDet|hexdet_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexDet/det.jsonl"
  "HexGenericRank|hexgenericrank_emit_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexGenericRank/generic.jsonl"
  "HexRank|hexrank_emit_fixtures|scripts/oracle/rank_carriers.py|conformance-fixtures/HexRank/rank.jsonl"
  "HexHermite|hexhermite_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexHermite/hermite.jsonl"
  "HexSmith|hexsmith_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexSmith/smith.jsonl"
  "HexCharPoly|hexcharpoly_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexCharPoly/charpoly.jsonl"
  "HexMinPoly|hexminpoly_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexMinPoly/minpoly.jsonl"
  "HexGramSchmidt|hexgramschmidt_emit_fixtures|scripts/oracle/gs_flint.py|conformance-fixtures/HexGramSchmidt/gram_schmidt.jsonl"
  "HexRealRoots|hexrealroots_emit_fixtures|scripts/oracle/realroots_flint.py|conformance-fixtures/HexRealRoots/realroots.jsonl"
  "HexSignDet|hexsigndet_json_bytes|scripts/oracle/sign_det_json_bytes.py|conformance-fixtures/HexSignDet/json-bytes.jsonl"
  "HexSignDet|hexsigndet_emit_fixtures|scripts/oracle/sign_det_flint.py|conformance-fixtures/HexSignDet/sign_det.jsonl"
  "HexSignDet|hexsigndet_emit_field_signs|scripts/oracle/sign_det_field_signs.py|conformance-fixtures/HexSignDet/field-signs.jsonl"
  "HexSignDet|hexsigndet_emit_common_fields|scripts/oracle/sign_det_common_fields.py|conformance-fixtures/HexSignDet/common-fields.jsonl"
  "HexRCF|hexrcf_emit_fixtures|scripts/oracle/rcf_flint.py|conformance-fixtures/HexRCF/rcf.jsonl"
  "HexRoots|hexroots_emit_fixtures|scripts/oracle/roots_flint.py|conformance-fixtures/HexRoots/roots.jsonl"
  "HexRealAlgebraic|hexrealalgebraic_emit_fixtures|scripts/oracle/real_algebraic_flint.py|conformance-fixtures/HexRealAlgebraic/real_algebraic.jsonl"
  # Pinned Z3 RCF, exact nested-infinitesimal roots
  "HexSignDet|hexsigndet_emit_infinitesimal|scripts/oracle/sign_det_z3.py|conformance-fixtures/HexSignDet/infinitesimal.jsonl"
  "HexSignDet|hexsigndet_emit_nested_fields|scripts/oracle/sign_det_nested_z3.py|conformance-fixtures/HexSignDet/nested-fields.jsonl"
  "HexOrderedFn|hexorderedfn_emit_fixtures|scripts/oracle/ordered_fn_z3.py|conformance-fixtures/HexOrderedFn/infinitesimal.jsonl"
  "HexOrderedFn|hexorderedfn_emit_real_fixtures|scripts/oracle/ordered_fn_real.py|conformance-fixtures/HexOrderedFn/real.jsonl"
  # SymPy backed
  "HexKronecker|hexkronecker_emit_fixtures|scripts/oracle/kronecker_sympy.py|conformance-fixtures/HexKronecker/identities.jsonl"
  "HexPolyDet|hexpolydet_emit_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexPolyDet/det.jsonl"
  "HexBareiss|hexbareiss_emit_carrier_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexBareiss/carriers.jsonl"
  "HexDeterminant|hexdeterminant_emit_carrier_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexDeterminant/carriers.jsonl"
  "HexCharPoly|hexcharpoly_emit_carrier_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexCharPoly/carriers.jsonl"
  "HexDet|hexdet_emit_carrier_fixtures|scripts/oracle/matrix_carriers.py|conformance-fixtures/HexDet/carriers.jsonl"
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
  "HexPrimality|hexprimality_squfof_measure|scripts/oracle/primality_squfof.py|conformance-fixtures/HexPrimality/squfof-corpus.jsonl"
  "HexECPP|hexecpp_emit_fixtures|scripts/oracle/ecpp_pari.py|conformance-fixtures/HexECPP/ecpp.jsonl"
  "HexECPP|hexecpp_emit_class_polynomials|scripts/oracle/ecpp_class_polynomials.py|conformance-fixtures/HexECPP/class-polynomials.jsonl"
  "HexIntFactor|hexintfactor_emit_fixtures|scripts/oracle/intfactor_pari.py|conformance-fixtures/HexIntFactor/intfactor.jsonl"
  "HexNumberField|hexnumberfield_emit_fixtures|scripts/oracle/number_field_flint_pari.py|conformance-fixtures/HexNumberField/number_field.jsonl"
  "HexNumberFieldTower|hexnumberfieldtower_emit_fixtures|scripts/oracle/number_field_tower_pari.py|conformance-fixtures/HexNumberFieldTower/number_field_tower.jsonl"
  # Exact Python integer/Fraction formula evaluation
  "HexRealFormula|hexrealformula_emit_fixtures|scripts/oracle/real_formula.py|conformance-fixtures/HexRealFormula/formula.jsonl"
  "HexRealClosure|hexrealclosure_trivial_conformance|scripts/oracle/real_closure_trivial.py|conformance-fixtures/HexRealClosure/trivial.jsonl"
  "HexRealClosure|hexrealclosure_bounds_conformance|scripts/oracle/real_closure_bounds.py|conformance-fixtures/HexRealClosure/bounds.jsonl"
  "HexRealClosure|hexrealclosure_deflation_conformance|scripts/oracle/real_closure_deflation.py|conformance-fixtures/HexRealClosure/deflation.jsonl"
  "HexRealClosure|hexrealclosure_isolation_conformance|scripts/oracle/real_closure_isolation.py|conformance-fixtures/HexRealClosure/isolation.jsonl"
  "HexRealClosure|hexrealclosure_policy_conformance|scripts/oracle/real_closure_policies.py|conformance-fixtures/HexRealClosure/policies.jsonl"
  "HexRealClosure|hexrealclosure_sample_conformance|scripts/oracle/real_closure_samples.py|conformance-fixtures/HexRealClosure/samples.jsonl"
  # Exact Python integer/Fraction Cartesian enumeration
  "HexLatticeEnum|hexlatticeenum_emit_fixtures|scripts/oracle/lattice_enum.py|conformance-fixtures/HexLatticeEnum/latticeenum.jsonl"
  # Conway tables backed
  "HexConway|hexconway_emit_fixtures|scripts/oracle/conway_luebeck.py|conformance-fixtures/HexConway/conway.jsonl"
  # pinned external nauty 2.9.3 backed (vendored source, project shim)
  "HexGraphIso|hexgraphiso_emit_fixtures|scripts/oracle/graphiso_nauty.py|conformance-fixtures/HexGraphIso/graphiso.jsonl"
  "HexGraphIso|hexgraphiso_emit_sparse|scripts/oracle/graphiso_nauty.py|conformance-fixtures/HexGraphIso/sparse.jsonl"
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
if [ "$mode" != "--build-only" ] && [ "${HEX_REQUIRE_ORACLES:-0}" = "1" ]; then
  if ! command -v gap >/dev/null 2>&1; then
    echo "FAIL: required GAP oracle is unavailable" >&2
    exit 1
  fi
  if ! python3 - <<'PY'
import flint
import cypari2
import conway_polynomials
import sympy
import z3
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
if library_selected HexRealClosure; then
  emits+=("hexrealclosure_trivial_tests")
fi
if library_selected HexRealClosure || library_selected HexSignDet; then
  emits+=("hexrealclosure_codec_bytes")
fi
if [ "${#emits[@]}" -gt 0 ] && ! lake build "${emits[@]}"; then
  echo "FAIL: building emit executables" >&2
  exit 1
fi
if [ "$mode" = "--build-only" ]; then
  exit 0
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

  # The byte-parser oracle supplies untrusted inputs to the compiled driver.
  if [ "$oracle" = "scripts/oracle/sign_det_json_bytes.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_sign_det_json_bytes ||
        ! python3 "$oracle" --check "$fixture" --exe ".lake/build/bin/$emit" ||
        ! python3 scripts/oracle/sign_det_json_stress.py --ci --exe ".lake/build/bin/$emit"; then
      echo "FAIL: $lib :: integer-only JSON byte conformance"
      return 1
    fi
    echo "OK: $lib :: integer-only JSON byte conformance"
    return 0
  fi

  # This compiled-input oracle runs the committed corpus through the measured
  # native executable; its input fixture is checked by independent division.
  if [ "$oracle" = "scripts/oracle/primality_squfof.py" ]; then
    if ! python3 "$oracle" --exe ".lake/build/bin/$emit" --corpus "$fixture"; then
      echo "FAIL: $lib :: SQUFOF divisor oracle reported a divergence"
      return 1
    fi
    echo "OK: $lib"
    return 0
  fi

  local emit_command=(".lake/build/bin/$emit")
  if [ "$oracle" = "scripts/oracle/real_closure_trivial.py" ]; then
    # Operational CI bound; manual validation retains the complete driver
    # without a limit. This does not set a scientific performance budget.
    if timeout 3600 env LEAN_ABORT_ON_PANIC=1 .lake/build/bin/hexrealclosure_trivial_tests; then
      :
    else
      local native_status=$?
      if [ "$native_status" -eq 124 ]; then
        echo "TIMEOUT: native rational-tower backend differential tests exceeded 3600 seconds" >&2
      else
        echo "FAIL: native rational-tower backend differential tests (exit $native_status)" >&2
      fi
      return 1
    fi
    emit_command=(env LEAN_ABORT_ON_PANIC=1 "${emit_command[@]}")
  fi
  if ! "${emit_command[@]}" >"$fresh"; then
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

  if [ "$oracle" = "scripts/oracle/matrix_carriers.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_matrix_carriers; then
      echo "FAIL: $lib :: carrier oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/sign_det_flint.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_sign_det_flint; then
      echo "FAIL: $lib :: oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/sign_det_common_fields.py" ] ||
      [ "$oracle" = "scripts/oracle/sign_det_field_signs.py" ]; then
    local test_class=CommonFieldOracle
    if [ "$oracle" = "scripts/oracle/sign_det_field_signs.py" ]; then
      test_class=FieldSignOracle
    fi
    if ! python3 -m unittest "scripts.oracle.test_sign_det_common_fields.$test_class"; then
      echo "FAIL: $lib :: common-field oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/sign_det_z3.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_sign_det_z3; then
      echo "FAIL: $lib :: infinitesimal oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/sign_det_nested_z3.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_sign_det_nested_z3; then
      echo "FAIL: $lib :: nested-field oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/real_closure_trivial.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_trivial; then
      echo "FAIL: native trivial-root oracle mutation tests" >&2
      return 1
    fi
  fi
  if [ "$oracle" = "scripts/oracle/real_closure_bounds.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_bounds; then
      echo "FAIL: $lib :: finite-bound oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/real_closure_policies.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_policies; then
      echo "FAIL: $lib :: RootSet policy oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/real_closure_isolation.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_isolation; then
      echo "FAIL: $lib :: isolation completion oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/real_closure_samples.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_samples; then
      echo "FAIL: $lib :: section/sector sample oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/real_closure_deflation.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_real_closure_deflation; then
      echo "FAIL: $lib :: exact-deflation oracle rejection checks failed"
      return 1
    fi
  fi

  if [ "$oracle" = "scripts/oracle/ordered_fn_z3.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_ordered_fn_z3; then
      echo "FAIL: $lib :: ordered-function oracle rejection checks failed"
      return 1
    fi
  fi
  if [ "$oracle" = "scripts/oracle/ordered_fn_real.py" ]; then
    if ! python3 -m unittest scripts.oracle.test_ordered_fn_real; then
      echo "FAIL: $lib :: ordered-function oracle rejection checks failed"
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

# Native context capacity covers the owning library and its JSON dependency.
if library_selected HexRealClosure || library_selected HexSignDet; then
  context_start=$SECONDS
  if ! (PYTHONPATH=scripts/oracle python3 -c \
      'from pathlib import Path; from sign_det_json_stress import check_stack; check_stack(Path(".lake/build/bin/hexrealclosure_codec_bytes"))' &&
      ulimit -s 8192 && LEAN_MAIN_USE_THREAD=0 LEAN_STACK_SIZE_KB=8192 \
      .lake/build/bin/hexrealclosure_codec_bytes 1000000); then
    echo "Conformance: native context codec capacity failed." >&2
    exit 1
  fi
  printf 'TIMING: HexRealClosure (hexrealclosure_codec_bytes) %ss\n' "$((SECONDS - context_start))"
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
