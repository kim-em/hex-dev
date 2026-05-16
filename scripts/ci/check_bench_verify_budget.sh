#!/usr/bin/env bash
# Time-budget wrapper enforcing SPEC/benchmarking.md §CI integration
# "Time budget" subsection.
#
# Runs `lake exe X_bench list && lake exe X_bench verify` for each
# bench-exe name passed on stdin or as args, captures wallclock per
# invocation, prints a sorted breakdown, emits `::warning::`
# annotations for libraries over the per-library soft threshold, and
# exits non-zero if the total wallclock exceeds the hard cap.
#
# Env knobs:
#   BENCH_VERIFY_WARN_SECONDS     per-library soft warning threshold
#                                  (default 30; warn-only, doesn't fail)
#   BENCH_VERIFY_HARD_CAP_SECONDS repo-wide hard cap (default 600 =
#                                  10 min); 0 disables.
#   BENCH_VERIFY_WARN_ONLY        if set to "1", report timings but
#                                  never fail on the hard cap. Used
#                                  for the initial rollout per HO-35
#                                  so we collect telemetry before
#                                  flipping the switch.
#
# Run from the repository root, after `lake build`. Intended for
# `.github/workflows/ci.yml`'s `build` job; also safe to run locally.

set -euo pipefail

warn_threshold="${BENCH_VERIFY_WARN_SECONDS:-30}"
hard_cap="${BENCH_VERIFY_HARD_CAP_SECONDS:-600}"
warn_only="${BENCH_VERIFY_WARN_ONLY:-0}"

if [ "$#" -eq 0 ]; then
  echo "usage: $0 <bench_exe_name> [<bench_exe_name> ...]" >&2
  exit 2
fi

# `gha_warn`: emit a workflow-command warning when running under GitHub
# Actions (where `$GITHUB_ACTIONS == true`); otherwise just print to
# stderr.
gha_warn() {
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "::warning::$*"
  else
    echo "WARNING: $*" >&2
  fi
}

# Per-bench timings, accumulated as "seconds bench_name" lines.
results_file="$(mktemp)"
trap 'rm -f "$results_file"' EXIT

total=0
for bench in "$@"; do
  echo "::group::$bench"
  start=$(date +%s)
  # Run list + verify as a pair. GitHub Actions builds these executables
  # in the preceding step, so prefer the binary directly there; `lake exe`
  # can spend the smoke budget on Lake replay checks rather than bench
  # verification. Local runs keep `lake exe` so stale binaries are rebuilt.
  bench_exe=".lake/build/bin/$bench"
  if [ "${GITHUB_ACTIONS:-}" = "true" ] && [ -x "$bench_exe" ]; then
    "$bench_exe" list
    "$bench_exe" verify
  else
    lake exe "$bench" list
    lake exe "$bench" verify
  fi
  end=$(date +%s)
  elapsed=$((end - start))
  total=$((total + elapsed))
  printf '%d %s\n' "$elapsed" "$bench" >> "$results_file"
  echo "::endgroup::"

  if [ "$elapsed" -gt "$warn_threshold" ]; then
    gha_warn "$bench verify took ${elapsed}s (> ${warn_threshold}s soft threshold). See SPEC/benchmarking.md §CI integration \"Time budget\"."
  fi
done

# Sorted breakdown — slowest first.
echo
echo "=== Bench verify wallclock breakdown ==="
sort -rn "$results_file" | awk '{ printf "  %5ds  %s\n", $1, $2 }'
echo "  -----"
printf '  %5ds  TOTAL\n' "$total"
echo

if [ "$hard_cap" -gt 0 ] && [ "$total" -gt "$hard_cap" ]; then
  msg="Bench verify total ${total}s exceeded hard cap ${hard_cap}s. See SPEC/benchmarking.md §CI integration \"Time budget\"."
  if [ "$warn_only" = "1" ]; then
    gha_warn "$msg (warn-only stage; would fail if BENCH_VERIFY_WARN_ONLY were unset)"
  else
    echo "FAIL: $msg" >&2
    echo "Per-library breakdown above. Fix the slowest contributor first:" >&2
    echo "  - Smoke settings leaking from scientific tuning? Add a smoke override clause." >&2
    echo "  - Genuinely slow at the smallest honest input? File a bench-found issue and roll back per SPEC/benchmarking.md §verdict-as-bug-trigger." >&2
    echo "  - DO NOT lower scientific settings to dodge the cap (verdict-laundering per §Anti-patterns)." >&2
    exit 1
  fi
fi

echo "check_bench_verify_budget: OK (${total}s total, hard cap ${hard_cap}s, warn-only=${warn_only})."
