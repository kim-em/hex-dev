#!/usr/bin/env bash
# Exercise every compiled carry-less-multiply path in HexGF2/ffi/clmul.c.
#
# `HexGF2/SPEC/hex-gf2.md` requires that tests exercise each compiled wrapper
# path. A build selects its path with preprocessor guards, so one build runs
# exactly one of them: the Lake target passes only `-O3`, which means ordinary
# builds compile the portable fallback and never the intrinsic. This script
# compiles the self-test a second time with the flags that enable an intrinsic,
# so both paths are checked on every CI run rather than each machine silently
# testing whichever one it happens to select.
#
# Extends the existing single job (SPEC/CI.md "no parallelism in CI"); it is a
# few seconds of `cc`, not a new runner.
set -euo pipefail

cd "$(dirname "$0")/../.."

CC="${CC:-cc}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

SRC="HexGF2/ffi/clmul.c"
TEST="HexGF2/ffi/clmul_selftest.c"

# `HEX_CLMUL_NO_LEAN` drops the Lean export wrapper, so the self-test compiles
# the arithmetic alone and needs neither Lean's headers nor its runtime.
COMMON=(-DHEX_CLMUL_NO_LEAN -O2)

build_and_run() {
  local label="$1"; shift
  local out="$WORK/selftest_$label"
  echo "--- $label ---"
  # No skip-on-failure path. The point of this script is that both compiled
  # paths run; a build that quietly declines to compile the intrinsic and exits
  # zero reports success for a check that did not happen. Architectures with no
  # intrinsic path at all are handled by not calling this for them.
  if ! "$CC" "${COMMON[@]}" "$@" "$SRC" "$TEST" -o "$out" 2>"$WORK/err_$label"; then
    cat "$WORK/err_$label" >&2
    echo "check_clmul_paths: the $label build must compile" >&2
    exit 1
  fi
  "$out"
}

# The path ordinary builds take.
build_and_run portable

# The intrinsic path for this architecture. `-msse4.1` is needed alongside
# `-mpclmul`: the x86 wrapper reads the high half of the product with
# `_mm_extract_epi64`, which is SSE4.1, and with only `-mpclmul` the compiler
# refuses to inline it.
ARCH="$(uname -m)"
case "$ARCH" in
  x86_64 | amd64)
    build_and_run pclmul -mpclmul -msse4.1 -DHEX_CLMUL_SELFTEST_EXPECT_INTRINSIC
    ;;
  aarch64 | arm64)
    build_and_run pmull -march=armv8-a+crypto -DHEX_CLMUL_SELFTEST_EXPECT_INTRINSIC
    ;;
  *)
    echo "check_clmul_paths: no intrinsic path defined for $ARCH; portable only"
    ;;
esac

echo "check_clmul_paths: OK"
