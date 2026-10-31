#!/usr/bin/env bash
# Check bounded monomial operations and both modular row-reduction paths.
# The Lean conformance module checks the wrapper's ownership and aliasing.
set -euo pipefail
cd "$(dirname "$0")/../.."
row_probe_dir="$(mktemp -d)"
trap 'rm -rf "$row_probe_dir"' EXIT
row_probe_cc="${CC:-cc}"
for variant in native remainder; do
  row_probe_flags=(-O2 -std=c11 -Wall -Wextra -Werror)
  if [ "$variant" = remainder ]; then
    row_probe_flags+=(-DHEX_GROEBNER_NO_UINT128)
  fi
  if [ "${HEX_GROEBNER_SANITIZE:-0}" = 1 ]; then
    row_probe_flags+=(-fsanitize=address,undefined -fno-omit-frame-pointer)
  fi
  "$row_probe_cc" "${row_probe_flags[@]}" HexGroebner/ffi/row_update_selftest.c -o "$row_probe_dir/$variant"
  "$row_probe_dir/$variant"
done
