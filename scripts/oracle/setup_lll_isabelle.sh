#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CACHE_DIR="${REPO_ROOT}/.cache/oracles/lll-isabelle"
ARCHIVE="${CACHE_DIR}/Experiments_LLL.zip"
SRC_DIR="${CACHE_DIR}/src"
PATCH_DIR="${REPO_ROOT}/scripts/oracle/patches/lll-isabelle"
URL="https://zenodo.org/record/2636367/files/Experiments_LLL.zip"
SHA256="5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0"
BINARY="${SRC_DIR}/experiments/svp_verified"

mkdir -p "${CACHE_DIR}"

if [[ -x "${BINARY}" ]]; then
  printf '%s\n' "${BINARY}"
  exit 0
fi

for tool in curl unzip make ghc shasum; do
  if ! command -v "${tool}" >/dev/null 2>&1; then
    printf 'setup_lll_isabelle.sh: required tool not found: %s\n' "${tool}" >&2
    exit 1
  fi
done

tmp="${CACHE_DIR}/tmp"
rm -rf "${tmp}"
mkdir -p "${tmp}"

if [[ ! -f "${ARCHIVE}" ]]; then
  curl -L --fail -o "${ARCHIVE}" "${URL}"
fi

actual="$(shasum -a 256 "${ARCHIVE}" | awk '{print $1}')"
if [[ "${actual}" != "${SHA256}" ]]; then
  printf 'setup_lll_isabelle.sh: sha256 mismatch for %s\n' "${ARCHIVE}" >&2
  printf 'expected: %s\nactual:   %s\n' "${SHA256}" "${actual}" >&2
  exit 1
fi

unzip -q "${ARCHIVE}" -d "${tmp}"

if compgen -G "${PATCH_DIR}"'/*.patch' >/dev/null; then
  for patch in "${PATCH_DIR}"/*.patch; do
    patch -d "${tmp}" -p1 < "${patch}"
  done
fi

rm -rf "${SRC_DIR}"
mv "${tmp}" "${SRC_DIR}"

make -C "${SRC_DIR}/experiments" svp_verified >/dev/null
printf '%s\n' "${BINARY}"
