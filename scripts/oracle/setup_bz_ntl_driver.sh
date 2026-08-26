#!/usr/bin/env bash
# Compile the persistent NTL factorization comparator driver consumed by the
# the cross-system factor sweep and print the path of the built binary on stdout.
#
# The compiled binary is cached at
#   $HEX_ORACLE_CACHE/bz-ntl/bz_ntl_service
# (default: $repo_root/.cache/oracles/bz-ntl/), keyed by the SHA-256 of the
# `bz_ntl_service.cc` source and the detected NTL CFLAGS/LDFLAGS so a
# refreshed source recompiles without manual cache invalidation.
#
# NTL discovery order:
#   1. `pkg-config --cflags --libs ntl` if present
#   2. `brew --prefix ntl` (macOS Homebrew)
#   3. system include path with `-lntl`
#
# Set `HEX_BZ_NTL_DRIVER` to a pre-built binary to skip compilation entirely.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cache_root="${HEX_ORACLE_CACHE:-${repo_root}/.cache/oracles}/bz-ntl"
binary="${cache_root}/bz_ntl_service"
fingerprint_file="${cache_root}/fingerprint"
src="${repo_root}/scripts/oracle/bz_ntl_service.cc"

if [[ -n "${HEX_BZ_NTL_DRIVER:-}" ]]; then
  printf '%s\n' "${HEX_BZ_NTL_DRIVER}"
  exit 0
fi

mkdir -p "${cache_root}"

lock_dir="${cache_root}/setup.lock"

acquire_lock() {
  local waited=0
  while ! mkdir "${lock_dir}" 2>/dev/null; do
    if [[ -f "${lock_dir}/pid" ]]; then
      local lock_pid
      lock_pid="$(cat "${lock_dir}/pid" 2>/dev/null || true)"
      if [[ "${lock_pid}" =~ ^[0-9]+$ ]] && ! kill -0 "${lock_pid}" 2>/dev/null; then
        rm -rf "${lock_dir}"
        continue
      fi
    fi
    if (( waited >= 300 )); then
      echo "setup_bz_ntl_driver.sh: timed out waiting for ${lock_dir}" >&2
      exit 1
    fi
    sleep 1
    waited=$((waited + 1))
  done
  printf '%s\n' "$$" > "${lock_dir}/pid"
  trap 'rm -rf "${lock_dir}"' EXIT
}

acquire_lock

need() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "setup_bz_ntl_driver.sh: missing required command: $1" >&2
    exit 1
  fi
}

need shasum

# Pick a C++ compiler.
cxx="${CXX:-}"
if [[ -z "${cxx}" ]]; then
  if command -v c++ >/dev/null 2>&1; then
    cxx=c++
  elif command -v g++ >/dev/null 2>&1; then
    cxx=g++
  elif command -v clang++ >/dev/null 2>&1; then
    cxx=clang++
  else
    echo "setup_bz_ntl_driver.sh: no C++ compiler found (set CXX)" >&2
    exit 1
  fi
fi

# Resolve NTL CFLAGS/LDFLAGS.
ntl_cflags=""
ntl_ldflags=""
if command -v pkg-config >/dev/null 2>&1 \
   && pkg-config --exists ntl 2>/dev/null; then
  ntl_cflags="$(pkg-config --cflags ntl)"
  ntl_ldflags="$(pkg-config --libs ntl)"
elif command -v brew >/dev/null 2>&1; then
  brew_prefix="$(brew --prefix ntl 2>/dev/null || true)"
  if [[ -n "${brew_prefix}" && -d "${brew_prefix}/include/NTL" ]]; then
    ntl_cflags="-I${brew_prefix}/include"
    ntl_ldflags="-L${brew_prefix}/lib -lntl"
    # GMP is an NTL dependency on most builds.
    gmp_prefix="$(brew --prefix gmp 2>/dev/null || true)"
    if [[ -n "${gmp_prefix}" && -d "${gmp_prefix}/include" ]]; then
      ntl_cflags="${ntl_cflags} -I${gmp_prefix}/include"
      ntl_ldflags="${ntl_ldflags} -L${gmp_prefix}/lib -lgmp"
    else
      ntl_ldflags="${ntl_ldflags} -lgmp"
    fi
  fi
fi
if [[ -z "${ntl_ldflags}" ]]; then
  # Fall back to system paths; NTL ships as `libntl` and pulls GMP.
  ntl_ldflags="-lntl -lgmp"
fi

fingerprint="$(printf '%s\n%s\n%s\n%s\n%s\n' \
  "$(shasum -a 256 "${src}" | awk '{print $1}')" \
  "${cxx}" \
  "${ntl_cflags}" \
  "${ntl_ldflags}" \
  "v1" \
  | shasum -a 256 | awk '{print $1}')"

if [[ -x "${binary}" && -f "${fingerprint_file}" \
      && "$(cat "${fingerprint_file}")" == "${fingerprint}" ]]; then
  printf '%s\n' "${binary}"
  exit 0
fi

echo "setup_bz_ntl_driver.sh: compiling ${binary}" >&2
# shellcheck disable=SC2086
"${cxx}" -O2 -std=c++17 ${ntl_cflags} "${src}" ${ntl_ldflags} -lpthread \
  -o "${binary}.tmp" >&2
mv "${binary}.tmp" "${binary}"
printf '%s\n' "${fingerprint}" > "${fingerprint_file}"
printf '%s\n' "${binary}"
