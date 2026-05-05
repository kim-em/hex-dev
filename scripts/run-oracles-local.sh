#!/usr/bin/env bash
# Bootstrap a virtualenv with the system and python dependencies
# required for an oracle driver under scripts/oracle/, then dispatch
# the JSONL stream from stdin (or extra args) to that driver.
#
# Usage:
#   scripts/run-oracles-local.sh <oracle> [args...] [< fixtures.jsonl]
#
# Examples:
#   scripts/run-oracles-local.sh poly_flint < fixtures.jsonl
#   lake exe hexpoly_emit_fixtures | scripts/run-oracles-local.sh poly_flint
#   scripts/run-oracles-local.sh poly_flint --check
#   scripts/run-oracles-local.sh hensel_pari --check
#
# Supported oracles map to system + pip dependencies:
#   poly_flint, berlekamp_flint, bz_flint, matrix_flint  → python-flint
#   hensel_pari                                          → cypari2 (+libpari)
#
# Platform detection picks one of:
#   * NixOS  — re-exec under `nix shell` with the required nixpkgs.
#   * macOS  — `brew install` any missing system libraries.
#   * Ubuntu — `sudo apt-get install` any missing system libraries.
#
# Re-runs with the same oracle skip every install step that already
# succeeded.  Force a clean slate by removing `.venv-oracles/`.

set -euo pipefail

die() { printf 'run-oracles-local: error: %s\n' "$*" >&2; exit 1; }
log() { printf 'run-oracles-local: %s\n' "$*" >&2; }

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VENV_DIR="$REPO_ROOT/.venv-oracles"
VENV_PY="$VENV_DIR/bin/python3"

usage() {
  awk 'NR>1 && /^#($| )/ {sub(/^# ?/, ""); print; next} NR>1 {exit}' \
    "${BASH_SOURCE[0]}"
}

oracle="${1:-}"
case "$oracle" in
  ""|-h|--help)
    usage
    [ -z "$oracle" ] && exit 1 || exit 0
    ;;
esac
shift
oracle_path="$REPO_ROOT/scripts/oracle/${oracle}.py"
[ -f "$oracle_path" ] \
  || die "unknown oracle '$oracle' (see $REPO_ROOT/scripts/oracle/*.py)"

# Per-oracle dependency declarations.
case "$oracle" in
  poly_flint|berlekamp_flint|bz_flint|matrix_flint)
    pip_packages="python-flint"
    need_pari=0
    need_fplll=0
    ;;
  hensel_pari)
    pip_packages="cypari2"
    need_pari=1
    need_fplll=0
    ;;
  *)
    # Unknown driver: install the full toolchain so a future oracle
    # dispatches without a script edit.
    pip_packages="python-flint cypari2 fpylll"
    need_pari=1
    need_fplll=1
    ;;
esac

detect_os() {
  case "$(uname -s)" in
    Darwin) echo macos ;;
    Linux)
      if [ -r /etc/os-release ] && grep -q '^ID=nixos$' /etc/os-release; then
        echo nixos
      elif command -v apt-get >/dev/null 2>&1; then
        echo ubuntu
      else
        echo unknown
      fi
      ;;
    *) echo unknown ;;
  esac
}

os="$(detect_os)"

# NixOS: re-exec under `nix shell` so pip can compile against the
# right C libraries.  The HEX_ORACLE_NIX_REENTERED guard prevents an
# infinite loop if the user is already inside a suitable shell.
if [ "$os" = nixos ] && [ -z "${HEX_ORACLE_NIX_REENTERED:-}" ]; then
  nix_pkgs=()
  [ "$need_pari"  = 1 ] && nix_pkgs+=(nixpkgs#pari)
  [ "$need_fplll" = 1 ] && nix_pkgs+=(nixpkgs#fplll)
  if [ ${#nix_pkgs[@]} -gt 0 ]; then
    command -v nix >/dev/null 2>&1 \
      || die "nix not found; install Nix or run inside a shell with the libraries"
    log "re-executing under nix shell ${nix_pkgs[*]}"
    export HEX_ORACLE_NIX_REENTERED=1
    exec nix shell "${nix_pkgs[@]}" --command \
      "${BASH_SOURCE[0]}" "$oracle" "$@"
  fi
fi

# macOS: brew install missing system libraries.
if [ "$os" = macos ]; then
  brew_pkgs=()
  [ "$need_pari"  = 1 ] && brew_pkgs+=(pari)
  [ "$need_fplll" = 1 ] && brew_pkgs+=(fplll)
  if [ ${#brew_pkgs[@]} -gt 0 ]; then
    command -v brew >/dev/null 2>&1 \
      || die "brew not found; install Homebrew before running this script"
    for pkg in "${brew_pkgs[@]}"; do
      if ! brew list --formula "$pkg" >/dev/null 2>&1; then
        log "brew install $pkg"
        brew install "$pkg"
      fi
    done
  fi
fi

# Ubuntu: apt-get install missing system libraries.
if [ "$os" = ubuntu ]; then
  apt_pkgs=(python3-venv)
  [ "$need_pari"  = 1 ] && apt_pkgs+=(libpari-dev pari-gp)
  [ "$need_fplll" = 1 ] && apt_pkgs+=(libfplll-dev)
  missing=()
  for pkg in "${apt_pkgs[@]}"; do
    if ! dpkg-query -W -f='${Status}' "$pkg" 2>/dev/null \
        | grep -q '^install ok installed$'; then
      missing+=("$pkg")
    fi
  done
  if [ ${#missing[@]} -gt 0 ]; then
    log "sudo apt-get install -y ${missing[*]}"
    sudo apt-get update -qq
    sudo apt-get install -y "${missing[@]}"
  fi
fi

if [ "$os" = unknown ]; then
  log "warning: unrecognised platform; assuming system libraries are already present"
fi

# Create the venv if missing.
if [ ! -x "$VENV_PY" ]; then
  command -v python3 >/dev/null 2>&1 || die "python3 not found"
  log "creating venv at $VENV_DIR"
  python3 -m venv "$VENV_DIR"
  "$VENV_PY" -m pip install --quiet --upgrade pip
fi

# Install only the python packages that aren't already importable.
missing_py=()
for pkg in $pip_packages; do
  case "$pkg" in
    python-flint) probe=flint ;;
    cypari2)      probe=cypari2 ;;
    fpylll)       probe=fpylll ;;
    *)            probe="$pkg" ;;
  esac
  if ! "$VENV_PY" -c "import $probe" >/dev/null 2>&1; then
    missing_py+=("$pkg")
  fi
done

if [ ${#missing_py[@]} -gt 0 ]; then
  log "pip install ${missing_py[*]}"
  "$VENV_PY" -m pip install --quiet "${missing_py[@]}"
fi

exec "$VENV_PY" "$oracle_path" "$@"
