#!/usr/bin/env bash
# Hard-fail gate enforcing SPEC/CI.md § "Mathlib cache is mandatory".
#
# After `lake exe cache get`, this script verifies the Mathlib package's
# olean cache is populated on disk. It exits non-zero if no Mathlib
# .olean files are present, or if the count is implausibly small;
# either case would cause subsequent `lake build` calls to silently
# rebuild Mathlib from source — the regression mode that produced the
# 24-hour CI queue this gate exists to prevent.
#
# Run from the repository root, after `lake exe cache get`. Intended
# for use inside `.github/workflows/*.yml`; also safe to run locally.

set -euo pipefail

# Search anywhere under .lake/ for olean files whose path contains
# /Mathlib/. The exact build-output layout has shifted across Lake
# versions; an unconditional search is robust to that.
mathlib_oleans=$(
  find .lake -type f -name '*.olean' -path '*/Mathlib/*' 2>/dev/null \
    | head -10000 \
    | wc -l \
    | tr -d '[:space:]'
) || mathlib_oleans=0

# Floor chosen well below current Mathlib size (~6000 oleans at
# v4.30) but high enough to catch the "totally empty" disaster case
# and partial fetches. Bump if Mathlib shrinks dramatically.
floor=4000

if [ "$mathlib_oleans" -lt "$floor" ]; then
  echo "FAIL: only $mathlib_oleans Mathlib .olean files found under .lake/;" >&2
  echo "      expected at least $floor. Cache is missing or incomplete." >&2
  echo "      Refusing to proceed; \`lake build\` would silently rebuild" >&2
  echo "      Mathlib from source. See SPEC/CI.md." >&2
  echo "      Diagnostic dump (first 30 olean paths under .lake/, if any):" >&2
  find .lake -type f -name '*.olean' 2>/dev/null | head -30 | sed 's/^/        /' >&2 || true
  echo "      Diagnostic dump (.lake build dirs):" >&2
  find .lake -maxdepth 6 -type d -name build 2>/dev/null | sed 's/^/        /' >&2 || true
  exit 1
fi

echo "OK: $mathlib_oleans Mathlib .olean files present under .lake/."
