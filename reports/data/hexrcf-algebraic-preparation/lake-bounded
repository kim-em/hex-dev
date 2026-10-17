#!/usr/bin/env bash
set -euo pipefail
hex_build_environment=(--setenv="PATH=$PATH" --setenv=LEAN_NUM_THREADS=2)
for hex_build_key in HEX_RCF_CELL_OUTPUT HEX_RCF_ZERO_OUTPUT HEX_RCF_ALGEBRAIC_CELL_OUTPUT; do
  if [[ -v "$hex_build_key" ]]; then
    hex_build_environment+=("--setenv=$hex_build_key=${!hex_build_key}")
  fi
done
exec systemd-run --user --wait --pipe --collect \
  --unit=hex-10358-lean-build \
  --property=MemoryMax=32G \
  --property=MemorySwapMax=0 \
  --property=OOMPolicy=kill \
  --working-directory="$PWD" \
  "${hex_build_environment[@]}" \
  /run/current-system/sw/bin/lake "$@"
