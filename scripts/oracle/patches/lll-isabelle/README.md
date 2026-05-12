# Isabelle LLL Oracle Patches

Patch files in this directory are applied by
`scripts/oracle/setup_lll_isabelle.sh` after unpacking the Zenodo
`Experiments_LLL.zip` archive and before building `svp_verified`.

## `01-persistent-stdin.patch`

Rewrites `haskell_sources/Main_Verified.hs` so `svp_verified` loops on
stdin instead of taking a single matrix file path on argv. Each line of
stdin is one matrix in Haskell's `[[Integer]]` read syntax; each line of
stdout is the squared norm emitted by `test_verified`. The binary
exits cleanly on EOF.

This shape is required by `SPEC/benchmarking.md` (post-#3657)
"External comparators / Process call": per-call GHC start-up plus
`readFile` is ~22 ms on the audit host, which dominates the wall time of
sub-millisecond LLL inputs and makes the comparator ratio dishonest.
After this patch, per-call protocol overhead measured by piping 1000
trivial inputs through the binary is ~30 µs.

The Hex-side wiring in `HexLLL/Bench.lean` spawns the driver lazily,
caches the process handle in an `IO.Ref`, sends one request line per
call, and parses one reply line back. On process death the wiring
re-spawns once and retries; persistent failure surfaces as an
`IO.userError`.
