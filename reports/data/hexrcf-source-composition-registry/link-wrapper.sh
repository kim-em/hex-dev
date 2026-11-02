#!/usr/bin/env bash
set -euo pipefail
export PROG=/home/kim/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin-unwrapped/ld.lld
exec /nix/store/gvp88ba8lnv8vhijhqlg6314b7yfjprm-elan-4.2.4/nix-support/ld-wrapper.sh "$@"
