#!/usr/bin/env bash
# Hard-fail gate enforcing SPEC/CI.md § "Mathlib cache is mandatory".
#
# After `lake exe cache get`, this script verifies the Mathlib package's
# olean cache is populated on disk. It exits non-zero if the cache is
# missing or implausibly small, which would cause subsequent
# `lake build` calls to silently rebuild Mathlib from source — the
# regression mode that produced the 24-hour CI queue this gate exists
# to prevent.
#
# Run from the repository root, after `lake exe cache get`. Intended
# for use inside `.github/workflows/*.yml`; also safe to run locally.

set -euo pipefail

# Search every directory Lake might place Mathlib oleans in. The exact
# layout has shifted across Lake versions and depending on whether
# Mathlib is the workspace package or a dependency, so we search
# rather than hardcoding a path.
candidate_roots=(
  ".lake/packages/mathlib/.lake/build/lib/Mathlib"
  ".lake/packages/mathlib/build/lib/Mathlib"
  ".lake/build/lib/Mathlib"
  "lake-packages/mathlib/build/lib/Mathlib"
)

found=""
for root in "${candidate_roots[@]}"; do
  if [ -d "$root" ]; then
    found="$root"
    break
  fi
done

if [ -z "$found" ]; then
  echo "FAIL: no Mathlib olean directory found under .lake/." >&2
  echo "      Searched:" >&2
  for root in "${candidate_roots[@]}"; do
    echo "        - $root" >&2
  done
  echo "      \`lake exe cache get\` did not produce a recognised cache layout." >&2
  echo "      Top-level .lake contents (for triage):" >&2
  find .lake -maxdepth 4 -type d 2>/dev/null | head -40 | sed 's/^/        /' >&2 || true
  echo "      See SPEC/CI.md." >&2
  exit 1
fi

olean_count=$(find "$found" -type f -name '*.olean' | wc -l | tr -d '[:space:]')

# Floor chosen well below current Mathlib size (~6000 oleans at
# v4.30) but high enough to catch the "totally empty" disaster case
# and partial fetches. Bump if Mathlib shrinks dramatically.
floor=4000

if [ "$olean_count" -lt "$floor" ]; then
  echo "FAIL: only $olean_count Mathlib .olean files in $found;" >&2
  echo "      expected at least $floor. Cache is incomplete." >&2
  echo "      Refusing to proceed; \`lake build\` would silently rebuild" >&2
  echo "      Mathlib from source. See SPEC/CI.md." >&2
  exit 1
fi

echo "OK: $olean_count Mathlib .olean files present in $found."
