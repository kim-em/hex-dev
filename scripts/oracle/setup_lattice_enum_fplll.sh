#!/usr/bin/env bash
# Build the informational comparator against installed fplll 5.5.0.
# Dependencies: C++17, pkg-config, fplll 5.5.0, GMP C++ and MPFR development headers.
# Prints the executable path; honours CXX and HEX_ORACLE_CACHE.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
version="$(pkg-config --modversion fplll)"
if [[ "$version" != 5.5.0 ]]; then
  echo "lattice comparator requires fplll 5.5.0, found $version" >&2
  exit 1
fi
cache="${HEX_ORACLE_CACHE:-${root}/.cache/oracles}/lattice-enum-fplll"
mkdir -p "$cache"
read -r -a flags <<< "$(pkg-config --cflags --libs fplll)"
"${CXX:-c++}" -std=c++17 -O2 "$root/scripts/oracle/lattice_enum_fplll.cc" \
  "${flags[@]}" -lgmpxx -o "$cache/lattice_enum_fplll"
printf '%s\n' "$cache/lattice_enum_fplll"
