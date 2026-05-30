#!/usr/bin/env bash
# scripts/profile/run_profile.sh — profile a hex bench target under
# samply, filtered to the bench library's timed regions.
#
# This is a thin wrapper around the lean-bench-samply orchestrator
# (https://github.com/kim-em/lean-bench-samply). It assumes:
#
#   - lean-bench-samply is checked out at $LEAN_BENCH_SAMPLY_HOME,
#     or at the default location ~/projects/lean-bench-samply.
#   - samply >= 0.13.1 is on PATH, and on macOS `samply setup` has
#     been run once to codesign the binary (see SPEC/profiling.md).
#   - The bench exe was built against a lean-bench version that
#     includes the `LeanBench.TimedRegions` module (the env-var
#     handshake the postprocessor depends on).
#
# Usage:
#   scripts/profile/run_profile.sh BENCH_EXE BENCH_NAME [PARAM [TARGET_NANOS]]
#
# Example:
#   scripts/profile/run_profile.sh \
#       .lake/build/bin/hexlll_bench \
#       Hex.LLLBench.runFirstShortVectorRandomBoundedChecksum \
#       120 5000000000
#
# Writes the filtered profile to:
#   /tmp/hex-profile-<bench-name>-<param>.json.gz
# and prints a diagnostics block (retained sample count,
# off-thread noise, calibration anchors). Load the resulting
# *.json.gz in the Firefox Profiler at https://profiler.firefox.com,
# or feed it to _scratch/profile_categories.py for a leaf-cost
# categorisation.
set -euo pipefail

BENCH_EXE="${1:?usage: run_profile.sh BENCH_EXE BENCH_NAME [PARAM [TARGET_NANOS]]}"
BENCH_NAME="${2:?usage: run_profile.sh BENCH_EXE BENCH_NAME [PARAM [TARGET_NANOS]]}"
PARAM="${3:-0}"
TARGET_NANOS="${4:-1000000000}"

LEAN_BENCH_SAMPLY_HOME="${LEAN_BENCH_SAMPLY_HOME:-$HOME/projects/lean-bench-samply}"
ORCHESTRATOR="$LEAN_BENCH_SAMPLY_HOME/scripts/profile_bench.py"

if [[ ! -f "$ORCHESTRATOR" ]]; then
  echo "error: lean-bench-samply orchestrator not found at $ORCHESTRATOR" >&2
  echo "       set LEAN_BENCH_SAMPLY_HOME or clone https://github.com/kim-em/lean-bench-samply" >&2
  exit 1
fi

SHORT_NAME="${BENCH_NAME##*.}"
OUT="/tmp/hex-profile-${SHORT_NAME}-${PARAM}.json.gz"

exec python3 "$ORCHESTRATOR" \
  --bench-exe "$BENCH_EXE" \
  --bench-name "$BENCH_NAME" \
  --param "$PARAM" \
  --target-nanos "$TARGET_NANOS" \
  --out "$OUT" \
  --samply-args "--rate 999 --unstable-presymbolicate"
