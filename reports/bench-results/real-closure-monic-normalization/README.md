# Monic-clean production packing

The [protocol](protocol.md) was committed before collection at
`4a80db8067598654aa26234867ddd93191a4aa1c`. All 48 fixed trial-major observations completed
on automatically leased CPU 64. All expected-hash checks passed.
Every raw export, command log and host observation is retained in
[capture/](capture/metadata.json); no sample exclusion or rerun occurred.

The standalone `Level` driver calls the actual production
`Algebraic.Element` kernels and enables their existing monic remainder path.
Its root contexts use `Unit` bindings and rational base coefficients. These
observations include its callback/encoding wrappers and do not measure the
construction or overhead of the full `Tower.Context` interface.

Starting with alpha₀ = 2, each level selects the positive root of
`(X² - alphaᵢ₋₁)(X - 3)` in `(0,2]`. Every context reports
`canReduce = true`; production packing supplies all remainders. The workload
is `(1 + alpha)^m / (alpha - 3)` at the top level. There is no extra eager
reduction or irreducibility fast path.

| Depth | Products m | Median ms | Full range ms | Stored bytes | Query graph bytes |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 2 | 0.067896 | 0.067606–0.068374 | 21 | 2093 |
| 1 | 4 | 0.121233 | 0.120371–0.121993 | 26 | 2260 |
| 1 | 8 | 0.229567 | 0.227978–0.231371 | 33 | 2600 |
| 1 | 16 | 0.485331 | 0.477239–0.490758 | 45 | 3280 |
| 2 | 2 | 4.892965 | 4.864028–4.932323 | 88 | 4278 |
| 2 | 4 | 9.728855 | 9.665135–9.879862 | 101 | 5865 |
| 2 | 8 | 24.106136 | 23.927612–24.289393 | 120 | 8237 |
| 2 | 16 | 60.778224 | 59.785992–61.105322 | 158 | 13300 |

Each child auto-tunes its inner repeats with a 0.5-second target. Per-call
time is `total_nanos / inner_repeats`; [analysis.json](analysis.json) retains
every per-call value and batch count. Setup precedes timing. The measured
body includes runtime input retrieval, product/division, production packing
and encoding/hashing. Final sign evidence and native reading/replay are
outside timing.

At depth one the stored degree is 2; at depth two it is 2 at both levels.
The eight endpoints therefore respect the cubic defining-head remainder
bound. At m = 16, maximum rational numerator/denominator bits are 33/3
at depth one and 37/8 at depth two; total coefficient bits are 95 and 348.
Final query graphs are single leaves (one node, zero edges, one occurrence).
These cases provide no certificate-sharing ablation or general depth
size/replay recurrence.

## Exact input and executable validation

- [Functional packets](functional.jsonl) retain all eight defining-head,
  stored-value and root/query graph outputs. Native readers/replay pass.
- [Pinned FLINT checks](functional-oracle.json) independently use
  Q(gamma), gamma^(2^depth) = 2, to check selected definitions, values, signs
  and literal growth. Graph statistics are structural; mathematical replay
  is checked by the native driver, rather than claimed by the Python oracle.
- Eight oracle tests include changed family/branch flags and coupled scaling
  of a defining head that preserves its roots. All pass. The original two
  nonmonic fixture outputs remain byte-identical; their six tests still pass.
- All eight named monic benchmark smoke checks pass.
- Executable SHA-256: `5a0cd7469e5836b1e65ef1b7a2bbaa06a9c779ed2b4420e7d50a049bc8419f8e`.
- [Build binding](build-binding.log) records the committed source and binary
  hash beside [the target build](build.log), before collection.
- [Registration source](source/NestedNormalization.lean.txt),
  [toolchain](source/lean-toolchain), [manifest](source/lake-manifest.json),
  protocol and all raw observations are retained.

These are fixed-family observations with no asymptotic verdict. The roots
and defining heads differ from the nonmonic family, so their times are not
a matched storage-policy comparison. Repeated zero tests, the three-way
policy/head/irreducibility attribution, remaining stages/families and general
DAG size/replay evidence remain required for Phase 4.

## Untimed operation counts

The separate [count protocol](counters-protocol.md) was committed at
`087312b7d5f652ef6710014236853aa0cae2ac38` before two diagnostic runs.
[Build bindings](counts/build.json), complete stdout/stderr and
[independent value/trace checks](counts/oracle.json) retain both results.
Their functional packets exactly match the earlier m = 16 endpoints.
These counts exclude preparation, final queries and encoding. The diagnostic
binary is separate from the timed executable; no diagnostic timing is used.

| Depth | Top-level products | Polynomial gcd | Polynomial xgcdLeft | Lean integer gcd | GMP integer gcd |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 17 | 1 | 1 | 4513 | 4513 |
| 2 | 17 | 59 | 59 | 402242 | 402242 |

Each top level calls add, sub, inverse, division, split, inverse-gcd and
inverse-xgcd once. The depth-two workload additionally reaches 58 predecessor
inversions, accounting for its 59 polynomial gcd and xgcdLeft entries.
Generic polynomial xgcd, pseudo-gcd and GMP gcdext entries are zero in both
runs. Base rational inverse callbacks are 50 and 4565, respectively; the
full callback inventory is retained by predecessor depth in each trace.
Polynomial workers, callbacks, Lean integer calls and GMP calls are separate
layers: their counts overlap and must not be added. In particular equal
Lean/GMP gcd counts do not represent twice as many gcd computations.
No counts of coefficient re-encoding or arbitrary evidence replay are inferred
from these observations.
