#!/usr/bin/env bash
# Build and run the non-default complete FKS2 conformance profile.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$repo_root"

exec lake exe hex_interval_pnt_fks2_local
