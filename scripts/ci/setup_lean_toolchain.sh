#!/usr/bin/env bash
# Install the exact stable/prerelease Lean pin from its canonical GitHub asset.
# Elan's distribution redirect has returned 404 for still-published prereleases,
# so CI puts the extracted toolchain itself on PATH and does not invoke a shim.

set -euo pipefail

: "${RUNNER_TEMP:?RUNNER_TEMP must name the runner scratch directory}"
: "${GITHUB_PATH:?GITHUB_PATH must name the Actions PATH command file}"

lean_toolchain=$(tr -d '[:space:]' < lean-toolchain)
case "$lean_toolchain" in
  leanprover/lean4:v*) ;;
  *)
    echo "::error::unsupported lean-toolchain pin: $lean_toolchain" >&2
    exit 1
    ;;
esac

lean_version=${lean_toolchain##*:}
lean_release=${lean_version#v}
lean_archive="lean-$lean_release-linux.tar.zst"
lean_url="https://github.com/leanprover/lean4/releases/download/$lean_version/$lean_archive"
lean_dir="$RUNNER_TEMP/hex-lean-toolchain"

mkdir -p "$lean_dir"
curl --fail --location --retry 3 --silent --show-error \
  --output "$RUNNER_TEMP/$lean_archive" "$lean_url"
tar --zstd --extract --file "$RUNNER_TEMP/$lean_archive" \
  --directory "$lean_dir" --strip-components=1

if [ ! -x "$lean_dir/bin/lean" ] || [ ! -x "$lean_dir/bin/lake" ]; then
  echo "::error::unexpected archive layout in $lean_archive" >&2
  exit 1
fi

lean_output=$($lean_dir/bin/lean --version)
if ! grep -Fq "$lean_release" <<< "$lean_output"; then
  echo "::error::resolved Lean is not $lean_version: $lean_output" >&2
  exit 1
fi

echo "$lean_dir/bin" >> "$GITHUB_PATH"
echo "$lean_output"
$lean_dir/bin/lake --version
