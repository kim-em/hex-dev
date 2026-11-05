#!/usr/bin/env bash
# Check bounded monomial operations, modular reduction and exact optional SIMD.
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
    row_probe_flags+=(-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer)
  fi
  "$row_probe_cc" "${row_probe_flags[@]}" HexGroebner/ffi/row_update_selftest.c -o "$row_probe_dir/$variant"
  "$row_probe_dir/$variant"
done
for variant in simd scalar; do
  row_probe_flags=(-O2 -std=c11 -Wall -Wextra -Werror)
  if [ "$variant" = scalar ]; then
    row_probe_flags+=(-DHEX_GROEBNER_NO_AVX2)
  fi
  if [ "${HEX_GROEBNER_SANITIZE:-0}" = 1 ]; then
    row_probe_flags+=(-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer)
  fi
  "$row_probe_cc" "${row_probe_flags[@]}" HexGroebner/ffi/matrix_scan_selftest.c -o "$row_probe_dir/$variant"
  "$row_probe_dir/$variant"
  "$row_probe_cc" "${row_probe_flags[@]}" HexGroebner/ffi/matrix_avx512_selftest.c -o "$row_probe_dir/$variant-avx512"
  "$row_probe_dir/$variant-avx512"
done

# Compile the actual production helper in both native and bytewise modes.
# Unused FFI entry points are discarded; this standalone test needs no Lean runtime.
row_probe_sdk="$(lean --print-prefix)"
for variant in native portable; do
  row_probe_flags=(-O2 -std=c11 -Wall -Wextra -Werror -ffunction-sections -fdata-sections
    "-I$row_probe_sdk/include")
  if [ "$(uname)" = Darwin ]; then
    row_probe_flags+=(-Wl,-dead_strip)
  else
    row_probe_flags+=(-Wl,--gc-sections)
  fi
  if [ "$variant" = portable ]; then row_probe_flags+=(-U__BYTE_ORDER__); fi
  if [ "${HEX_GROEBNER_SANITIZE:-0}" = 1 ]; then
    row_probe_flags+=(-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer)
  fi
  "$row_probe_cc" "${row_probe_flags[@]}" HexGroebner/ffi/matrix_index_selftest.c -o "$row_probe_dir/index-$variant"
  "$row_probe_dir/index-$variant"
done

trie_probe_flags=(-O2 -std=c11 -Wall -Wextra -Werror)
if [ "${HEX_GROEBNER_SANITIZE:-0}" = 1 ]; then
  trie_probe_flags+=(-fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-omit-frame-pointer)
fi
"$row_probe_cc" "${trie_probe_flags[@]}" HexGroebner/ffi/trie_selftest.c -o "$row_probe_dir/trie"
"$row_probe_dir/trie"

python3 scripts/ci/check_groebner_matrix.py
if [ "${HEX_GROEBNER_MATRIX_PROFILE:-regular}" = regular ]; then
  for matrix_profile in forced packed; do
    HEX_GROEBNER_NATIVE_LOG_DIR= \
      HEX_GROEBNER_MATRIX_PROFILE="$matrix_profile" HEX_GROEBNER_MATRIX_VARIANTS=Native \
      python3 scripts/ci/check_groebner_matrix.py
  done
fi
