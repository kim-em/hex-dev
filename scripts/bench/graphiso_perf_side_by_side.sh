#!/usr/bin/env bash
# Side-by-side CPU profile of the hex-graph-iso cactus binary.
#
# `hexgraphiso_cactus` runs `canonicalize` and the nauty comparator on the
# same instances in one process, so one `perf record` of it attributes
# every sample to one of these categories:
#
#   hex-search      compiled Lean code of the nauty-compatible search
#                   (`Hex.GraphIso.Nauty.*`, including `VSet` and `Bits`)
#   hex-instances   building the corpus instances (`Hex.GraphIso.Families`,
#                   `Random`, `Graph.ofRel`): the lazy adjacency functions
#                   the driver hands to `canonicalize`
#   hex-other       other compiled Lean code (List/Array/Nat library
#                   functions, the driver itself)
#   GMP+allocator   bignum arithmetic and the heap (`__gmp*`,
#                   `lean_nat_big_*`, `malloc`/`free`, mimalloc)
#   Lean-runtime    the rest of the Lean runtime (`lean_*`, `lean::`)
#   nauty-C         the vendored nauty 2.9.3 and its FFI shim
#
# Usage:
#   scripts/bench/graphiso_perf_side_by_side.sh [BINARY] [ARGS...]
#     record a run of BINARY (default .lake/build/bin/hexgraphiso_cactus,
#     built if absent; ARGS are passed through, e.g. a family name) and
#     print the category table
#   scripts/bench/graphiso_perf_side_by_side.sh --report PERF_DATA
#     print the table for an existing perf.data
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"

categorize() {
  python3 -c '
import re, sys
order = ["hex-search", "hex-instances", "hex-other", "GMP+allocator", "Lean-runtime", "nauty-C", "other"]
cats = {k: 0.0 for k in order}
top = []
line_re = re.compile(r"^\s*([0-9.]+)%\s+\[\.\]\s+(\S+)")
nauty = re.compile(r"^(refine|refine1|bestcell|nauty|firstpathnode|othernode|targetcell|maketargetcell|breakout|testcanlab|updatecan|isautom|fmperm|fmptn|orbjoin|shortprune|longprune|permset|cheapautom|doref|processnode|recover|firstterminal|hex_nauty_canon|densenauty|nauty_check|nautil_check|naugraph_check|nextelement|setautominfo|writeperm|putorbits|getbigcells|extra_autom|writegroupsize|dispatch_graph|mcrs|densenauty_check|sortindirect|orbjoin)")
def cat(sym):
    if sym.startswith("__gmp") or sym.startswith("lean_nat_big") or sym.startswith("mi_") or sym.startswith("_mi_") or sym.startswith("lean::mpz") or sym.startswith("lean_alloc") or sym.startswith("lean_free") or sym.startswith("lean_dealloc") or sym.split("@")[0] in ("malloc", "free", "cfree", "realloc", "calloc", "_int_malloc", "_int_free", "malloc_consolidate", "unlink_chunk"):
        return "GMP+allocator"
    if "GraphIso_Nauty" in sym or "GraphIso_VSet" in sym:
        return "hex-search"
    if "GraphIso_Families" in sym or "GraphIso_Random" in sym or "Graph_ofRel" in sym or "GraphIso_Graph" in sym:
        return "hex-instances"
    if sym.startswith("l_") or sym.startswith("lp_") or sym.startswith("_lean_main") or sym.startswith("initialize_"):
        return "hex-other"
    if sym.startswith("lean_") or sym.startswith("_ZN4lean") or sym.startswith("lean::"):
        return "Lean-runtime"
    if nauty.match(sym):
        return "nauty-C"
    return "other"
for line in sys.stdin:
    m = line_re.match(line)
    if not m:
        continue
    pct, sym = float(m.group(1)), m.group(2)
    cats[cat(sym)] += pct
    top.append((pct, sym))
total = sum(cats.values()) or 1.0
print("| category | share |")
print("|---|---|")
for k in order:
    print(f"| {k} | {100 * cats[k] / total:.1f}% |")
print()
print("top symbols:")
for pct, sym in sorted(top, reverse=True)[:20]:
    print(f"  {pct:5.1f}%  {sym}")
'
}

if [ "${1:-}" = "--report" ]; then
  data="$2"
else
  bin="${1:-.lake/build/bin/hexgraphiso_cactus}"
  shift || true
  if [ ! -x "$bin" ]; then
    lake build "$(basename "$bin")"
  fi
  data="/tmp/graphiso-perf-$(basename "$bin")-$$.data"
  perf record -q -F 2000 -o "$data" -- "$bin" "$@" > /dev/null
fi
perf report -i "$data" --stdio --no-children --sort symbol --percent-limit 0 2>/dev/null \
  | categorize
echo "perf data: $data"
