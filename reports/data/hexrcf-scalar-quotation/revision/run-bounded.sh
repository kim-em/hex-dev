#!/usr/bin/env bash
set -euo pipefail
exec systemd-run --user --wait --pipe --collect \
  --unit=hex-10358-lean-build \
  --property=MemoryMax=32G \
  --property=MemorySwapMax=0 \
  --property=OOMPolicy=kill \
  --working-directory="$PWD" \
  --setenv="PATH=$PATH" --setenv=LEAN_NUM_THREADS=2 \
  "$@"
