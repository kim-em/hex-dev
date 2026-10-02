# Shared real-formula performance

The Mathlib-free core has 34 compiled registrations covering structural operations,
validated serialization, and exact rational evaluation. All 34 agree with their
declared two-sided scaling models. Reification, semantic proofs, and the RCF
adapter use the separate [fresh-module proof report](hex-real-formula-mathlib-performance.md).

This is implementation evidence, not a claim that the repository's independent
review and phase-admission process is complete. Both new libraries are registered
at Phase 1; in particular the reifier's HexReflect dependencies are at Phase 1.

## Bench targets

Names below are in `Hex.RealFormula.Bench`. The model column copies each
`setup_benchmark` expression. Scientific timing includes complete structural
result consumption through `Hashable`; operation-only profiles exclude that
consumption. Implication and biconditional can share their inputs in memory,
but consumption visits the expanded result. The DAG ladder contains `n+1`
stored nodes and `2*n+1` expanded tree nodes; this is separate from potentially
exponential expansion of arbitrary DAGs.

| Target | Declared model | Parameter range | Median at largest parameter (µs) | Residual slope β |
| --- | --- | --- | ---: | ---: |
| `move` | `n` | 64–2048 | 1312.114 | 0.0220 |
| `swap` | `n` | 64–2048 | 104.134 | -0.0074 |
| `nnf` | `n` | 64–2048 | 346.622 | 0.0260 |
| `evaluateKernel` | `n` | 64–2048 | 4806.623 | 0.0044 |
| `view` | `n` | 64–2048 | 65.975 | 0.0065 |
| `evalBits` | `n` | 65536–2097152 | 363.741 | -0.0184 |
| `ofView` | `n` | 64–2048 | 47.403 | -0.0155 |
| `lift` | `n` | 64–2048 | 1405.272 | 0.0102 |
| `renameTerms` | `n * Nat.log2 (n + 1)` | 32–1024 | 663.855 | -0.0250 |
| `validate` | `n` | 64–2048 | 77.153 | 0.0164 |
| `drop` | `n` | 64–2048 | 1298.875 | 0.0133 |
| `rename` | `n` | 64–2048 | 1261.663 | 0.0115 |
| `renameArity` | `n` | 64–2048 | 31.356 | -0.0279 |
| `evaluate` | `n` | 64–2048 | 6165.020 | -0.0042 |
| `decodeTerms` | `n * n` | 256–8192 | 385484.378 | -0.0595 |
| `decode` | `n` | 64–2048 | 1754.180 | -0.0131 |
| `evalExponent` | `Nat.log2 (n + 1)` | 256–281474976710656 | 9.496 | -0.0019 |
| `implication` | `n` | 64–2048 | 663.740 | -0.0145 |
| `encode` | `n` | 64–2048 | 615.260 | 0.0156 |
| `equality` | `n` | 64–2048 | 2.360 | -0.0798 |
| `prefixDecode` | `n` | 64–2048 | 71.690 | -0.0283 |
| `evalArity` | `n` | 64–2048 | 962.789 | -0.0036 |
| `nodes` | `n` | 64–2048 | 42.673 | 0.0394 |
| `polys` | `n` | 64–2048 | 217.797 | -0.0020 |
| `evalTerms` | `n` | 32–1024 | 2588.299 | 0.1432 |
| `prefixEquality` | `n` | 64–2048 | 2.440 | -0.0850 |
| `biconditional` | `n` | 64–2048 | 1212.864 | 0.0055 |
| `prefixNodes` | `n` | 64–2048 | 5.714 | -0.0033 |
| `prefixRename` | `n` | 64–2048 | 92.450 | -0.0328 |
| `prefixEncode` | `n` | 64–2048 | 53.694 | -0.0080 |
| `support` | `n` | 64–2048 | 77.948 | 0.0381 |
| `degree` | `n` | 64–2048 | 36.017 | 0.0179 |
| `dag` | `n` | 64–2048 | 59.181 | 0.0076 |
| `supportArity` | `n` | 64–2048 | 44.041 | -0.0022 |

Fixed-size atoms isolate syntax/prefix traversal. The monomial evaluation grid
has bounded exponents and uses valuation `(1,1)`; permutation renaming rebuilds
a balanced tree. Ascending raw terms exercise quadratic list insertion in
`Kernel.normalize` before tree reconstruction. Arity varies in a single monomial.
The coefficient-bit ladder multiplies an odd growing integer by `3/2`; the
exponent ladder uses valuation `1`, isolating binary powering without growing
rational numerators. These are independent families, not a claim of unit-cost
rational arithmetic on unrestricted inputs.

## Verdicts

All entries use mode 1 (two-sided parametric evidence):
`consistent_with_declared_complexity`, with no truncated budgets or failed rows.
The [complete export](data/hex-real-formula/compiled-final.jsonl) retains four
trial-major samples at each of six parameters, medians, ranges, result hashes,
RSS, and the harness verdicts. Each registration requests 100 ms inner batches;
the ordinary 20% leading-rung warmup removes one rung only from verdict fitting.
All completed samples remain available. No samples were removed for host load.

Run `python3 scripts/bench/real_formula_sweep.py compiled --output OUTPUT.jsonl`.
The runner leases an automatically selected CPU on the shared host. The recorded
run used CPU 2 on `chungus2`, AMD EPYC 9455, x86-64 NixOS, Lean 4.34.0. Timings
are host-specific observations. Exact command, load context, source SHA-256s,
and repository base are in the [context](data/hex-real-formula/compiled-final.context.json).
The run was made in a dirty implementation checkout based on
`72a5c75ffecdec60d53375c458abcdc59823b571`; the [exact measured source snapshots](data/hex-real-formula/final-sources/)
match those hashes. The pinned lean-bench revision is in that snapshot's
`lake-manifest.json.txt`.

The [initial export](data/hex-real-formula/compiled.jsonl) and
[optimized export](data/hex-real-formula/compiled-optimized.jsonl) are retained,
including their unsuccessful verdicts and corresponding source snapshots.
Initial prefix renaming and swapping exposed repeated closure traversal and
source-by-target exponent scans; list-to-vector decoding repeatedly indexed a
linked list. Proved `csimp` implementations now use an index table, scatter
exponents, and materialize list entries once. All logical definitions retain
their proved meaning. Larger coefficient and raw-term ladders separate fixed
and lower-order overhead from the declared model. The final run moves checksum
work into harness consumption so attribution profiles can exclude it. These
runs are not paired AB/BA comparisons; no before/after speedup is inferred.

## Comparator ratios

The formula SPEC names no external performance comparator. There are no
cross-system speed ratios or performance superiority claims. The independent
Python `Fraction` oracle checks 26 versioned fixture cases for correctness;
it is not used as a timing comparator.

## Profile

Each family has one operation-only `cycles:u` profile at 999 Hz, captured by
`perf` and imported into samply. `normalize_perf.py` verifies every imported
sample timestamp against the raw perf sequence before applying the monotonic
clock anchor. The unchanged lean-bench-samply filter selects the bench thread
and `kernel` intervals; preparation, result consumption, and exit are excluded.
Raw samples stay at the local paths in the manifests. Commands, profiler version
and revision, binary hashes, diagnostics, and artifact hashes are retained in
[data/hex-real-formula/profiles](data/hex-real-formula/profiles/).

| Family | Case / parameter | Retained samples | Timed ms | Calibration residual ms | Classified % | Leaf own / GMP / allocation / runtime % |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| syntax | `decode` / 32768 | 1197 | 1198.82 | 0.974 | 92.73 | 13.37 / 0.00 / 36.34 / 43.02 |
| monomials | `decodeTerms` / 8192 | 325 | 518.02 | 0.512 | 100.00 | 78.77 / 0.00 / 0.92 / 20.31 |
| arity | `evalArity` / 2048 | 933 | 931.67 | 0.988 | 92.18 | 1.29 / 36.76 / 41.26 / 12.86 |
| coefficient-bits | `evalBits` / 2097152 | 672 | 672.47 | 0.419 | 100.00 | 0.00 / 96.58 / 3.27 / 0.15 |
| exponents | `evalExponent` / 281474976710656 | 909 | 904.76 | 0.247 | 92.96 | 2.31 / 40.04 / 35.20 / 15.40 |

All retained profiles pass calibration, sample-count, and sensitivity checks.

**syntax.** Inclusive ranking: `Hex.RealFormula.Kernel.Body.decode` 100.00%; `Hex.MvPoly.Kernel.denote` 59.82%; `Hex.Mono.lex` 11.86%; `Hex.MvPoly.Kernel.monoFast` 9.86%.

**monomials.** Inclusive ranking: `Hex.MvPoly.Kernel.insert` 98.15%; `Hex.MvPoly.Kernel.expCmp` 40.92%; `Hex.MvPoly.Kernel.normalize` 1.85%; `Hex.MvPoly.Kernel.denote` 1.85%.

**arity.** Inclusive ranking: `Hex.RealFormula.QF.evalRat` 100.00%; `Hex.Mono.powBySq` 63.02%.

**coefficient-bits.** Inclusive ranking: `Hex.RealFormula.QF.evalRat` 86.31%.

**exponents.** Inclusive ranking: `Hex.RealFormula.QF.evalRat` 99.56%; `Hex.Mono.powBySq` 94.61%.

Syntax decoding traverses every Boolean node, checks exponent-vector lengths,
normalizes each fixed-size atom and reconstructs its polynomial tree. Its
allocation and runtime costs implement those traversals. Raw-term decoding
is dominated by the declared insertion normalization. Arity evaluation visits
all exponent coordinates, with rational/runtime arithmetic at each coordinate.
Coefficient-bit evaluation spends its dominant cost on large integer limbs,
while the exponent case traverses the binary exponent with bounded rational
values. These costs belong to their named registrations; inclusive percentages
can overlap and must not be summed.

The first direct samply capture contained no samples. Earlier wrapper-checksum
captures and the short low-confidence captures remain documented in
[profile-runs.json](data/hex-real-formula/profile-runs.json),
[profiles-with-wrapper-hashes](data/hex-real-formula/profiles-with-wrapper-hashes/),
and the profile manifests. They do not establish the final attribution result.
The short prefix-renaming windows did not satisfy sensitivity even after a
longer capture: shifting them by 5 ms mixed operation samples with result
consumption. The syntax representative therefore uses 32,768 prepared tree
units, producing longer decode regions. The exponent capture was lengthened
to meet the sample requirement. These are input/duration protocol changes,
not selection for a quieter host.

## Concerns

No unresolved mismatch remains on the declared ladders. Kernel list normalization
is intentionally quadratic on ascending raw terms. The measurements do not bound
arbitrary biconditional/prenex or DAG expansion: those operations remain
output-sensitive and the frontend enforces expansion and proof budgets.
The compiled measurements carry dirty-checkout provenance with exact snapshots;
clean-build proof evidence is reported separately. Neither evidence set substitutes
for the repository's independent review gates.
