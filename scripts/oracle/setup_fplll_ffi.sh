#!/usr/bin/env bash
# Build `kim-em/fplll-ffi` and print the path to its `libfplllffi` shared
# library — the FFI shim that exports `lean_fplll_lll_reduce`, the symbol the
# HexLLL provider hook (`HexLLL/ffi/lean_hexlll_provider.c`) resolves at
# runtime via `dlsym(RTLD_DEFAULT, ...)`.
#
# Usage:
#
#   HEX_FPLLL_FFI_LIB="$(scripts/oracle/setup_fplll_ffi.sh)"
#
# Honoured overrides:
#
#   HEX_FPLLL_FFI_REF    — git ref to check out (default: pinned hash below).
#   HEX_FPLLL_FFI_REPO   — repo URL (default: https://github.com/kim-em/fplll-ffi).
#   HEX_ORACLE_CACHE     — cache root (default: <repo>/.cache/oracles).
#
# The build uses the toolchain pinned by `fplll-ffi/lean-toolchain` via `elan`,
# vendors fplll-5.5.0 as a submodule, and dynamically links libfplll/GMP/MPFR.
# On Linux the runtime path to Lean's `libLake_shared.so` is supplied by the
# caller via `LD_LIBRARY_PATH`; on macOS via `DYLD_LIBRARY_PATH`.
set -euo pipefail

# Pinned fplll-ffi commit. Bump in lockstep with the SPEC / report updates.
default_ref="main"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cache_root="${HEX_ORACLE_CACHE:-${repo_root}/.cache/oracles}/fplll-ffi"
src_dir="${cache_root}/src"
repo_url="${HEX_FPLLL_FFI_REPO:-https://github.com/kim-em/fplll-ffi}"
ref="${HEX_FPLLL_FFI_REF:-${default_ref}}"

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
    if (( waited >= 900 )); then
      echo "setup_fplll_ffi.sh: timed out waiting for ${lock_dir}" >&2
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
    echo "setup_fplll_ffi.sh: missing required command: $1" >&2
    exit 1
  fi
}

need git
need elan
need make
need cc

case "$(uname -s)" in
  Darwin) shared_ext="dylib" ;;
  *)      shared_ext="so"    ;;
esac

clone_or_update() {
  if [[ ! -d "${src_dir}/.git" ]]; then
    rm -rf "${src_dir}"
    git clone --quiet "${repo_url}" "${src_dir}"
  fi
  git -C "${src_dir}" fetch --quiet --tags origin
  git -C "${src_dir}" checkout --quiet "${ref}"
  git -C "${src_dir}" submodule update --quiet --init --recursive
}

clone_or_update

# Install the toolchain pinned by fplll-ffi (matches hex's toolchain in
# practice, so this is a no-op when the two pin the same version). `lake`
# inside `src_dir` reads the local `lean-toolchain` file via elan, so no
# `+toolchain` prefix is needed once the toolchain is installed.
toolchain="$(tr -d '\r\n' < "${src_dir}/lean-toolchain")"
if ! elan toolchain list | grep -Fq "${toolchain}"; then
  elan toolchain install "${toolchain}" >&2
fi

lib_path="${src_dir}/.lake/build/lib/libfplllffi.${shared_ext}"

if [[ ! -f "${lib_path}" ]]; then
  (cd "${src_dir}" && lake build FPLLL >&2)
fi

if [[ ! -f "${lib_path}" ]]; then
  echo "setup_fplll_ffi.sh: build did not produce ${lib_path}" >&2
  exit 1
fi

printf '%s\n' "${lib_path}"
