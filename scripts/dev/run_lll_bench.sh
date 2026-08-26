#!/usr/bin/env bash
# Regenerate the HexLLL comparator/scaling bench data on a QUIET machine.
#
# Timings are only meaningful with no concurrent CPU load (concurrent builds
# inflate and lump the curves). Run this on an idle carica, then regenerate the
# SVGs with scripts/plots/hex-lll-comparator.py.
#
# Usage:  scripts/dev/run_lll_bench.sh <family> [<bench-filter>]
#   e.g.  scripts/dev/run_lll_bench.sh ajtai Ajtai
set -euo pipefail

family="${1:?usage: run_lll_bench.sh <family> <bench-filter>}"
filter="${2:-}"
cache="${HEX_ORACLE_CACHE:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)/.cache/oracles}"

export HEX_ORACLE_CACHE="$cache"
export HEX_FPLLL_FFI_LIB="$cache/fplll-ffi/shim/libfplllffi.$( [ "$(uname)" = Darwin ] && echo dylib || echo so )"
export HEX_LLL_ISABELLE_SVP="$cache/lll-isabelle/src/experiments/svp_verified"
export HEX_LLL_ISABELLE_CERTIFIED_SVP="$cache/lll-isabelle/src/experiments/svp_certified"

for b in "$HEX_FPLLL_FFI_LIB" "$HEX_LLL_ISABELLE_SVP" "$HEX_LLL_ISABELLE_CERTIFIED_SVP"; do
  [ -e "$b" ] || { echo "missing oracle: $b (run setup_fplll_ffi.sh / setup_lll_isabelle.sh)"; exit 1; }
done

# Warn (do not block) on a dirty tree / concurrent load: the export records
# git_dirty, and the numbers are only trustworthy on an idle machine.
[ -z "$(git status --porcelain)" ] || echo "WARN: working tree dirty; export env.git_dirty will be true."
load="$(uptime | sed 's/.*load average/load/')"
echo "machine $load -- ensure this is near-idle before trusting the timings."

commit="$(git rev-parse --short HEAD)"
mkdir -p reports/bench-results reports/figures
out="reports/bench-results/hex-lll-${family}-${commit}.json"

echo "running family=$family filter=${filter:-$family} -> $out"
# repeats=3 for committed numbers; the targets carry warm inner-batching
# (minTotalSeconds) so each point is a warm median. Floor target included so
# the Isabelle-certified per-request fork floor is subtracted by the plotter.
lake exe hexlll_bench run --filter "${filter:-$family}" --export-file "$out"
lake exe hexlll_bench run --filter IsabelleCertifiedProcessFloor \
  --export-file "reports/bench-results/hex-lll-${family}-floor-${commit}.json"

echo "done -> $out"
echo "now: python3 scripts/plots/hex-lll-comparator.py --family $family \\"
echo "       --isabelle-floor reports/bench-results/hex-lll-${family}-floor-${commit}.json"
