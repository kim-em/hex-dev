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

mathlib_lib_dir=".lake/packages/mathlib/.lake/build/lib/Mathlib"

if [ ! -d "$mathlib_lib_dir" ]; then
  echo "FAIL: $mathlib_lib_dir does not exist." >&2
  echo "      \`lake exe cache get\` did not populate the Mathlib cache." >&2
  echo "      Refusing to proceed; subsequent \`lake build\` would" >&2
  echo "      rebuild Mathlib from source. See SPEC/CI.md." >&2
  exit 1
fi

olean_count=$(find "$mathlib_lib_dir" -type f -name '*.olean' | wc -l | tr -d '[:space:]')

# Floor chosen well below current Mathlib size (~6000 oleans at
# v4.30) but high enough to catch the "totally empty" disaster case
# and partial fetches. Bump if Mathlib shrinks dramatically.
floor=4000

if [ "$olean_count" -lt "$floor" ]; then
  echo "FAIL: only $olean_count Mathlib .olean files in $mathlib_lib_dir;" >&2
  echo "      expected at least $floor. Cache is incomplete." >&2
  echo "      Refusing to proceed; \`lake build\` would silently rebuild" >&2
  echo "      Mathlib from source. See SPEC/CI.md." >&2
  exit 1
fi

echo "OK: $olean_count Mathlib .olean files present in cache."
