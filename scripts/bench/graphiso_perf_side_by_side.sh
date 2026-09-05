#!/usr/bin/env bash
# Side-by-side CPU profile of the hex-graph-iso cactus binary.
#
# `hexgraphiso_cactus` runs `canonicalize` and the nauty comparator on the
# same instances in one process, so one `perf record` of it attributes
# every sample to one of four categories:
#
#   hex-Lean       compiled Lean code of the search (symbols `l_Hex_*`
#                  and the other `l_*` Lean-generated functions)
#   GMP+allocator  bignum arithmetic and the heap (`__gmp*`,
#                  `lean_nat_big_*`, `malloc`/`free`, `lean_alloc*`)
#   Lean-runtime   the rest of the Lean runtime (`lean_*`, `Lean::`)
#   nauty-C        the vendored nauty 2.9.3 (`refine*`, `bestcell`,
#                  `nauty`, `hex_nauty_canon`, ...)
#
# Usage: scripts/bench/graphiso_perf_side_by_side.sh [BINARY] [ARGS...]
#   BINARY defaults to .lake/build/bin/hexgraphiso_cactus (built if absent)
#   ARGS are passed to the binary (e.g. a family name for a partial run).
# Writes perf.data under /tmp and prints the category table to stdout.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
bin="${1:-.lake/build/bin/hexgraphiso_cactus}"
shift || true
if [ ! -x "$bin" ]; then
  lake build "$(basename "$bin")"
fi
data="/tmp/graphiso-perf-$(basename "$bin")-$$.data"
perf record -q -F 2000 -o "$data" -- "$bin" "$@" > /dev/null
perf report -i "$data" --stdio --no-children --sort symbol --percent-limit 0 2>/dev/null \
  | python3 -c '
import re, sys
cats = {"hex-Lean": 0.0, "GMP+allocator": 0.0, "Lean-runtime": 0.0, "nauty-C": 0.0, "other": 0.0}
top = []
line_re = re.compile(r"^\s*([0-9.]+)%\s+\[\.\]\s+(\S+)")
nauty = re.compile(r"^(refine|refine1|bestcell|nauty|firstpathnode|othernode|targetcell|maketargetcell|breakout|testcanlab|updatecan|isautom|fmperm|fmptn|orbjoin|shortprune|longprune|permset|cheapautom|doref|processnode|recover|firstterminal|hex_nauty_canon|densenauty|densenauty_check|nauty_check|nautil_check|naugraph_check|nextelement|setautominfo|writeperm|putorbits|getbigcells|alloc_error|extra_autom|writegroupsize|dispatch_graph|EMPTYSET|mcrs)")
for line in sys.stdin:
    m = line_re.match(line)
    if not m:
        continue
    pct, sym = float(m.group(1)), m.group(2)
    if sym.startswith("__gmp") or sym.startswith("lean_nat_big") or sym in ("malloc", "free", "cfree", "realloc", "calloc", "_int_malloc", "_int_free", "malloc_consolidate", "unlink_chunk") or sym.startswith("lean_alloc") or sym.startswith("lean_free") or sym.startswith("lean_dealloc"):
        cats["GMP+allocator"] += pct
    elif sym.startswith("l_") or sym.startswith("_lean_main") or sym.startswith("initialize_"):
        cats["hex-Lean"] += pct
    elif sym.startswith("lean_") or sym.startswith("_ZN4lean") or sym.startswith("lean::"):
        cats["Lean-runtime"] += pct
    elif nauty.match(sym):
        cats["nauty-C"] += pct
    else:
        cats["other"] += pct
    top.append((pct, sym))
total = sum(cats.values())
print("| category | share |")
print("|---|---|")
for k, v in cats.items():
    print(f"| {k} | {100 * v / total:.1f}% |")
print()
print("top symbols:")
for pct, sym in sorted(top, reverse=True)[:15]:
    print(f"  {pct:5.1f}%  {sym}")
'
echo "perf data: $data"
