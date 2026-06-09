#!/usr/bin/env bash
set -euo pipefail

url="https://zenodo.org/records/2636367/files/Experiments_LLL.zip"
sha256="5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cache_root="${HEX_ORACLE_CACHE:-${repo_root}/.cache/oracles}/lll-isabelle"
archive="${cache_root}/Experiments_LLL.zip"
src_dir="${cache_root}/src"
mode="${1:-verified}"
case "${mode}" in
  verified|--verified)
    binary="${src_dir}/experiments/svp_verified"
    make_target="svp_verified"
    ;;
  certified|--certified)
    binary="${src_dir}/experiments/svp_certified"
    make_target="svp_certified"
    ;;
  *)
    echo "setup_lll_isabelle.sh: usage: $0 [verified|certified]" >&2
    exit 2
    ;;
esac
patch_dir="${repo_root}/scripts/oracle/patches/lll-isabelle"

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
      echo "setup_lll_isabelle.sh: timed out waiting for ${lock_dir}" >&2
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
    echo "setup_lll_isabelle.sh: missing required command: $1" >&2
    exit 1
  fi
}

need curl
need shasum
need unzip
need make
need ghc
if [[ "${make_target}" == "svp_certified" ]]; then
  need fplll
fi

verify_archive() {
  local path="$1"
  local actual
  actual="$(shasum -a 256 "${path}" | awk '{print $1}')"
  if [[ "${actual}" == "${sha256}" ]]; then
    return 0
  fi
  echo "setup_lll_isabelle.sh: SHA-256 mismatch for ${path}" >&2
  echo "  expected ${sha256}" >&2
  echo "  actual   ${actual}" >&2
  return 1
}

download_archive() {
  local tmp="${archive}.tmp"
  rm -f "${tmp}"
  curl -L --fail --silent --show-error --connect-timeout 20 \
    --retry 8 --retry-all-errors --retry-delay 10 --retry-max-time 900 \
    -o "${tmp}" "${url}"
  verify_archive "${tmp}"
  mv "${tmp}" "${archive}"
}

if [[ -f "${archive}" ]]; then
  if ! verify_archive "${archive}"; then
    rm -f "${archive}"
    download_archive
  fi
else
  download_archive
fi

if [[ ! -d "${src_dir}/experiments" ]]; then
  rm -rf "${src_dir}"
  mkdir -p "${src_dir}"
  unzip -q "${archive}" -d "${src_dir}"
fi

shopt -s nullglob
patches=("${patch_dir}"/*.patch)
if (( ${#patches[@]} > 0 )); then
  stamp="${cache_root}/patches-applied.stamp"
  current_patch_sum="$(shasum -a 256 "${patches[@]}" | shasum -a 256 | awk '{print $1}')"
  if [[ ! -f "${stamp}" ]] || [[ "$(cat "${stamp}")" != "${current_patch_sum}" ]]; then
    rm -rf "${src_dir}"
    mkdir -p "${src_dir}"
    unzip -q "${archive}" -d "${src_dir}"
    for patch in "${patches[@]}"; do
      patch -l -d "${src_dir}" -p1 < "${patch}" >&2
    done
    printf '%s\n' "${current_patch_sum}" > "${stamp}"
    rm -f "${src_dir}/experiments/svp_verified" "${src_dir}/experiments/svp_certified"
  fi
fi

if [[ ! -x "${binary}" ]]; then
  make -C "${src_dir}/experiments" "${make_target}" >/dev/null
fi

printf '%s\n' "${binary}"
