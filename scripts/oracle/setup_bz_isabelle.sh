#!/usr/bin/env bash
set -euo pipefail

url="https://www.isa-afp.org/release/afp-current.tar.gz"
sha256="51f0eea952b391b9053dd3eb30ba1736e1e8618ff005bf197c3b76a2b8a3c5c7"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cache_root="${HEX_ORACLE_CACHE:-${repo_root}/.cache/oracles}/bz-isabelle"
archive="${cache_root}/afp-current.tar.gz"
afp_dir="${cache_root}/afp"
afp_thys="${afp_dir}/thys"
build_dir="${cache_root}/wrapper"
code_dir="${build_dir}/code"
binary="${build_dir}/bz_isabelle"
template_dir="${repo_root}/scripts/oracle/bz-isabelle"

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
      echo "setup_bz_isabelle.sh: timed out waiting for ${lock_dir}" >&2
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
    echo "setup_bz_isabelle.sh: missing required command: $1" >&2
    exit 1
  fi
}

need curl
need shasum
need tar
need isabelle
need ghc

verify_archive() {
  local path="$1"
  local actual
  actual="$(shasum -a 256 "${path}" | awk '{print $1}')"
  if [[ "${actual}" == "${sha256}" ]]; then
    return 0
  fi
  echo "setup_bz_isabelle.sh: SHA-256 mismatch for ${path}" >&2
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

if [[ ! -f "${afp_thys}/Berlekamp_Zassenhaus/Factorization_External_Interface.thy" ]]; then
  rm -rf "${afp_dir}"
  mkdir -p "${afp_dir}"
  tar -xzf "${archive}" -C "${afp_dir}" --strip-components=1
fi

mkdir -p "${build_dir}"
cp "${template_dir}/ROOT" "${build_dir}/ROOT"
cp "${template_dir}/Hex_BZ_Export.thy" "${build_dir}/Hex_BZ_Export.thy"
cp "${template_dir}/Main.hs" "${build_dir}/Main.hs"

template_sum="$(
  shasum -a 256 \
    "${template_dir}/ROOT" \
    "${template_dir}/Hex_BZ_Export.thy" \
    "${template_dir}/Main.hs" |
    shasum -a 256 | awk '{print $1}'
)"
stamp="${build_dir}/template.stamp"

if [[ ! -f "${stamp}" ]] || [[ "$(cat "${stamp}")" != "${template_sum}" ]]; then
  rm -rf "${code_dir}" "${binary}" "${build_dir}"/*.hi "${build_dir}"/*.o
  mkdir -p "${build_dir}"
  cp "${template_dir}/ROOT" "${build_dir}/ROOT"
  cp "${template_dir}/Hex_BZ_Export.thy" "${build_dir}/Hex_BZ_Export.thy"
  cp "${template_dir}/Main.hs" "${build_dir}/Main.hs"
  printf '%s\n' "${template_sum}" > "${stamp}"
fi

afp_component_registered() {
  local component
  while IFS= read -r component; do
    if [[ -f "${component}/Berlekamp_Zassenhaus/Factorization_External_Interface.thy" ]]; then
      return 0
    fi
  done < <(isabelle components -l 2>/dev/null | awk '/^  / {print substr($0, 3)}')
  return 1
}

afp_build_args=()
if ! afp_component_registered; then
  afp_build_args=(-d "${afp_thys}")
fi

isabelle build "${afp_build_args[@]}" -o browser_info=false -o document=false \
  -b Berlekamp_Zassenhaus >/dev/null

if [[ ! -f "${code_dir}/Hex_BZ.hs" ]]; then
  isabelle build "${afp_build_args[@]}" -D "${build_dir}" \
    -o browser_info=false -o document=false Hex_BZ_Export >/dev/null
fi

if [[ ! -x "${binary}" || "${build_dir}/Main.hs" -nt "${binary}" || "${code_dir}/Hex_BZ.hs" -nt "${binary}" ]]; then
  ghc -O2 -i"${code_dir}" -outputdir "${build_dir}" \
    -o "${binary}" "${build_dir}/Main.hs" >/dev/null
fi

printf '%s\n' "${binary}"
