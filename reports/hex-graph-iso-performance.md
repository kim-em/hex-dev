# HexGraphIso Performance Report

## Bench Targets

The compiled suite owns each executable surface once. The first four rows are
parametric registrations with declared cost models; the remaining sixteen are
fixed benchmarks on committed circulant sizes, because the nauty-compatible
canonical search declares no polynomial model in `n`
(`HexGraphIso/SPEC/hex-graph-iso.md` Section Benchmarks).

| target | declared complexity or fixed purpose |
|---|---|
| `Hex.GraphIsoBench.runDenseConvert` | `n ^ 2` |
| `Hex.GraphIsoBench.runRefine` | `n ^ 3` |
| `Hex.GraphIsoBench.runRelabel` | `n ^ 2` |
| `Hex.GraphIsoBench.runReferenceCanon` | `n ^ n * n ^ 2` |
| `Hex.GraphIsoBench.runHexCanon{8,12,16}` | fixed public fast `canon` at the committed sizes |
| `Hex.GraphIsoBench.runHexCanonChecked{8,12,16}` | fixed certificate-checked `Checked.canon` twins |
| `Hex.GraphIsoBench.runNautyCanon{8,12,16}` | fixed pinned-comparator column joined on the canonical bits |
| `Hex.GraphIsoBench.runSpecKey6` | fixed reference canonical key at the exhaustive merge size |
| `Hex.GraphIsoBench.runIsIso12` | fixed public fast isomorphism decision |
| `Hex.GraphIsoBench.runIsIsoChecked12` | fixed certificate-checked decision twin |
| `Hex.GraphIsoBench.runFindIso12` | fixed witness-returning decision |
| `Hex.GraphIsoBench.runCertify12` | fixed unbounded certificate generation |
| `Hex.GraphIsoBench.runCertReplay12` | fixed generation-plus-replay pipeline |
| `Hex.GraphIsoBench.runCanonAgree16` | fixed agreement check joining the two comparator columns |

`runRelabel` and canonical graph comparison declare quadratic bit-matrix
models, a full dense refinement declares the SPEC's conservative cubic model,
and the reference canonical form declares the `n ^ n` candidate enumeration
with quadratic per-candidate work. Each derivation sits adjacent to its
`setup_benchmark` line in `bench/HexGraphIso/Bench.lean`, which is what
`scripts/check_phase4.py --all` enforces.

The declared input families are normative in
`HexGraphIso/SPEC/hex-graph-iso.md` Sections Reproducible generators and
Benchmarks, and map onto the recorded corpora as follows.

| family | corpus labels | role |
|---|---|---|
| `circulant-ladder` | `circulant-12`, `circulant-1248` | the bench driver's own inputs, and the widest `n` ladder in the sweep |
| `random-gnp` | `random` | `G(n, 1/2)` from the recorded SplitMix64 seeds, and the tactic probes' relabelled pair |
| `strongly-regular` | `paley`, `latin`, `johnson`, `kneser` | refinement's hard cases, including the `(25, 12, 5, 6)` pair `paley25` versus `latin5` |
| `grid-and-hypercube` | `grid`, `hypercube` | the sparse families on which refinement discretizes quickly |
| `decision-pairs` | `cycles`, `cycles-dense`, `irregular`, `named`, `srg` and the shared families | positive and negative pairs carrying the two decision tiers and the tactic tier |

Every canonicalization result is hashed from its ordered cell sizes,
upper-triangle adjacency bits, and label, so the comparator columns check exact
result agreement as well as timing.

## Verdicts

The compiled scientific record is
`reports/bench-results/hex-graph-iso-compiled-b5ebc89a0-chungus2.json`. It was
produced on `chungus2`, an AMD EPYC 9455 host, with Lean 4.34.0-rc2, pinned to
CPU 22, on 2026-09-03. The measured tree carries the release-preparation
working state, but `HexGraphIso/` and `bench/HexGraphIso/Bench.lean` are
byte-identical to commit `b5ebc89a0670622946f243bdacddb27daec6a81e`; the
uncommitted paths at measurement time were the proof probes, `libraries.yml`,
and a manual chapter heading, none of which enter this binary. All rows
reported hash agreement across every repeat. The exact command was:

```sh
taskset -c 22 lake exe hexgraphiso_bench run \
  Hex.GraphIsoBench.runDenseConvert Hex.GraphIsoBench.runRefine \
  Hex.GraphIsoBench.runRelabel Hex.GraphIsoBench.runReferenceCanon \
  Hex.GraphIsoBench.runHexCanon8 Hex.GraphIsoBench.runHexCanon12 \
  Hex.GraphIsoBench.runHexCanon16 Hex.GraphIsoBench.runHexCanonChecked8 \
  Hex.GraphIsoBench.runHexCanonChecked12 Hex.GraphIsoBench.runHexCanonChecked16 \
  Hex.GraphIsoBench.runNautyCanon8 Hex.GraphIsoBench.runNautyCanon12 \
  Hex.GraphIsoBench.runNautyCanon16 Hex.GraphIsoBench.runSpecKey6 \
  Hex.GraphIsoBench.runIsIso12 Hex.GraphIsoBench.runIsIsoChecked12 \
  Hex.GraphIsoBench.runFindIso12 Hex.GraphIsoBench.runCertify12 \
  Hex.GraphIsoBench.runCertReplay12 Hex.GraphIsoBench.runCanonAgree16 \
  --export-file reports/bench-results/hex-graph-iso-compiled-b5ebc89a0-chungus2.json
```

The four parametric registrations:

| target | harness verdict | slope residual `beta` | largest retained rung |
|---|---|---:|---:|
| `runDenseConvert` | inconclusive, observed **slower** | +0.271 | 4.126 ms at `n = 256` |
| `runRefine` | inconclusive, observed faster | -1.099 | 701.609 us at `n = 128` |
| `runRelabel` | consistent with declared complexity | -0.028 | 4.018 ms at `n = 256` |
| `runReferenceCanon` | inconclusive, observed faster | not derivable | 15.431 ms at `n = 6` |

`runRelabel` is the one clean two-sided result: its constant runs 64.957 down to
61.316 across `n = 32` to `256`, a 5.6% drift over an 8x size range, which is
what a validated quadratic bit-matrix model looks like.

`runRefine` and `runReferenceCanon` are the distinct one-sided verdict **within
declared upper bound (observed faster)**. Both models are deliberately
conservative: the SPEC declares a full dense refinement cubic as an upper bound
rather than an exponent claim, and `n ^ n * n ^ 2` is a gross bound on an
enumeration that prunes. `runReferenceCanon`'s constant falls monotonically
from 104.970 at `n = 2` to 9.187 at `n = 6`, so the harness cannot fit a slope
at all and reports no `beta`. These validate the upper bounds, not the
exponents, and are weaker than a two-sided validation by construction.

`runDenseConvert` is the one registration this run does **not** validate. Its
constant is flat at 26.633, 25.430, 25.331 across `n = 8, 16, 32` and then
rises to 62.960 at `n = 256`, a 2.5x climb that a quadratic model does not
predict. The `n = 64` and `n = 128` rungs fell below ten times the harness's
21.233 ms per-spawn floor and were excluded, so the verdict rests on a gap
between `n = 32` and `n = 256` with nothing in between. The timed region sinks
its result through `(Nauty.rowsOf G).foldl (· + ·) 0`, and `rowsOf` returns
`Array Nat` whose entries are `n`-bit bitsets, so the measurement includes a
GMP summation over operands that grow with `n` on top of the conversion itself.
That is a plausible source of the extra `n ^ 0.271` and it is a property of the
registration's sink rather than of `rowsOf`, but this run does not separate the
two, and the report does not claim the quadratic model holds. See Concerns.

Two of six rungs on `runDenseConvert` and `runRelabel`, and two of five on
`runRefine`, were below the per-spawn floor and excluded. That is the expected
shape for microsecond-scale bit operations under a process-spawning harness and
not a defect, but it does mean the parametric verdicts above rest on four,
three, four, and five retained rungs respectively.

The sixteen fixed benchmarks, five repeats each, all hashes agreeing:

| target | median | min | max |
|---|---:|---:|---:|
| `runNautyCanon8` | 5.054 us | 4.931 us | 5.107 us |
| `runNautyCanon12` | 9.629 us | 9.404 us | 9.726 us |
| `runNautyCanon16` | 15.666 us | 15.625 us | 15.959 us |
| `runHexCanon8` | 19.346 us | 19.192 us | 19.543 us |
| `runHexCanon12` | 32.336 us | 32.114 us | 32.496 us |
| `runHexCanon16` | 48.860 us | 48.234 us | 51.055 us |
| `runHexCanonChecked8` | 80.436 us | 79.429 us | 81.236 us |
| `runHexCanonChecked12` | 129.463 us | 128.449 us | 132.437 us |
| `runHexCanonChecked16` | 193.723 us | 193.034 us | 198.808 us |
| `runCanonAgree16` | 52.745 us | 52.217 us | 53.384 us |
| `runCertify12` | 91.049 us | 90.583 us | 91.750 us |
| `runIsIso12` | 112.635 us | 112.212 us | 116.592 us |
| `runFindIso12` | 113.701 us | 110.932 us | 116.613 us |
| `runCertReplay12` | 124.557 us | 124.278 us | 126.491 us |
| `runSpecKey6` | 125.904 us | 125.015 us | 128.196 us |
| `runIsIsoChecked12` | 506.786 us | 502.970 us | 525.419 us |

`runFindIso12` costs 1.1% more than `runIsIso12`, so returning the witness
permutation rather than the bit is free at this size. `runCertReplay12` costs
36.8% more than `runCertify12`, which is the price of replaying a certificate
over generating one. `runIsIsoChecked12` is 4.50x `runIsIso12`, the same
checked-tier factor the sweep reports below.

## Comparator ratios

The declared comparator is
**nauty 2.9.3 (vendored source, in-process FFI through Hex.BenchOracle.Nauty)**,
classified gating. Its required result is exact output agreement, and the first
release sets no speed-ratio requirement, so the ratios below are reported
without a threshold.

The gating condition holds exactly. On the fixed instances the two columns
agree bit for bit:

| size | hex canonical hash | nauty canonical hash | agree |
|---|---|---|---|
| 8 | `0xff8d6c4e25613e1c` | `0xff8d6c4e25613e1c` | yes |
| 12 | `0x3daf781bf38521d3` | `0x3daf781bf38521d3` | yes |
| 16 | `0x1e5791c7749acd6c` | `0x1e5791c7749acd6c` | yes |

`runHexCanonChecked{8,12,16}` and `runCertReplay12` and `runCanonAgree16`
report the same hashes as their fast twins, so the certificate-checked pipeline
and the replay pipeline agree with nauty as well. `runCanonAgree16` fails the
suite outright if the public canonical bits ever diverge, and it passed.

The speed ratios on the fixed sizes:

| size | nauty | hex fast | hex checked | fast / nauty | checked / nauty | checked / fast |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 5.054 us | 19.346 us | 80.436 us | 3.83 | 15.91 | 4.16 |
| 12 | 9.629 us | 32.336 us | 129.463 us | 3.36 | 13.44 | 4.00 |
| 16 | 15.666 us | 48.860 us | 193.723 us | 3.12 | 12.37 | 3.97 |

Breadth comes from the committed cactus sweep, not from the fixed rows. The
newest recorded sweep is fingerprint `b4e80b4517b7` on `chungus2`, dated
2026-09-03T08:37:23Z with label "manual revision and gpetersen family":
`reports/bench-results/hexgraphiso-cactus-b4e80b4517b7-chungus2.jsonl` (98
canonical-labelling instances, `n = 8` to `255`),
`hexgraphiso-pairs-b4e80b4517b7-chungus2.jsonl` (34 decision pairs, 18 positive
and 16 negative), and `hexgraphiso-tactic-b4e80b4517b7-chungus2.json`. Each
instance is the minimum of five repetitions after a warmup, sunk through a
`@[noinline]` black box, with a doubled-batch scaling self-check. The compiled
tiers have no timeout, so their curves are complete by construction rather than
by fitting a budget.

Geometric means over the 98 canonical-labelling instances, all three tiers
solving all 98:

| tier | geometric mean | median | max | ratio to nauty |
|---|---:|---:|---:|---:|
| nauty | 71.306 us | 59.343 us | 3.379 ms | 1.00 |
| hex fast (`canonicalize`) | 667.440 us | 338.672 us | 212.765 ms | 9.36 |
| hex checked (`Checked.canonicalize`) | 3.165747 ms | 1.751888 ms | 1.030087 s | 44.40 |

The geometric-mean checked-over-fast ratio is **4.74**, ranging from 2.75 on
`grid14x14` to 12.35 on `paley53`. Both extremes of the nauty ratio fall on the
hardest instances: `fast / nauty` peaks at 62.96 on `kneser22-2` and
`checked / nauty` at 386.33 on `johnson20-2`.

Per corpus family, geometric means:

| corpus family | count | `n` range | fast | checked | nauty | checked / fast | fast / nauty |
|---|---:|---|---:|---:|---:|---:|---:|
| `random` | 18 | 10-255 | 388 us | 1.209 ms | 58 us | 3.12 | 6.74 |
| `grid` | 10 | 9-225 | 441 us | 1.422 ms | 62 us | 3.23 | 7.17 |
| `circulant-12` | 17 | 8-255 | 421 us | 1.978 ms | 57 us | 4.70 | 7.37 |
| `hypercube` | 5 | 8-128 | 268 us | 1.513 ms | 29 us | 5.65 | 9.28 |
| `circulant-1248` | 12 | 17-225 | 801 us | 3.858 ms | 97 us | 4.81 | 8.25 |
| `paley` | 13 | 13-229 | 796 us | 5.832 ms | 78 us | 7.33 | 10.15 |
| `latin` | 3 | 25-169 | 2.252 ms | 10.958 ms | 139 us | 4.87 | 16.22 |
| `johnson` | 10 | 10-231 | 1.475 ms | 9.414 ms | 91 us | 6.38 | 16.25 |
| `kneser` | 10 | 10-231 | 1.859 ms | 10.587 ms | 109 us | 5.69 | 17.02 |

This is the report's central quantitative claim, and it is a claim about
constants, not about asymptotics. Conformance pins the visited-node counters,
so hex and nauty traverse exactly the same search tree on every input in this
corpus. Every number in the `fast / nauty` column is therefore a per-node
constant factor of a Lean implementation against a C one, never an algorithmic
difference, and it runs from 6.74 on the sparse random family to 17.02 on the
dense Kneser family.

The checked tier's 4.74x geometric-mean overhead is the current price of
validating every answer through the certificate checker. It is expected to
collapse, not shrink: the verified search refinement programme in
`HexGraphIso/SPEC/hex-graph-iso.md` Section Verified search refinement attaches
the checked guarantees to the fast path itself, at which point there is no
separate checked tier to price. Until that programme lands, the honest reading
of this report is that the shipped fast path is 6.7x to 17.0x nauty and the
shipped verified path is a further 4.7x on top.

Two caveats on the sweep. First, `python3 scripts/bench/check_graphiso_sweep_freshness.py`
fails on this branch: the newest recorded sweep is `b4e80b4517b7`, which
corresponds to commit `1690b550b`, and the branch's relevant-source
fingerprint has moved past it. Nothing that moved it changes a measured code
path: the release-preparation commits relocated the SPEC and touched
`HexGraphIso/Families.lean`, and the Phase-6 commit added docstrings and
renamed two declarations. The fingerprint is a source hash, so it moves anyway.
The branch needs one sweep regeneration before it lands, and these numbers are
measured one commit behind it. Second, the sweep's free-text label mentions a "gpetersen family" that is
not in the corpus: the instance set is byte-identical to the preceding sweep
`5059deb32f57`, so `b4e80b4517b7` is a re-measurement rather than a corpus
change. The label is unvalidated free text and the corpus is what the data
says.

## Profile

The tactic tier is where a profile is owed, because it is the tier with no
compiled analogue, and the fresh-module probes are its profile. The SPEC
mandates four release cases; all four close, on this host, with Lean
4.34.0-rc2, on 2026-09-03. Each module was invalidated by appending a unique
comment, rebuilt through `lake build`, and then restored; three interleaved
samples per module for the merge-build cases and two for the scheduled one.

| SPEC release case | module | raw samples (s) | median (s) | delta to baseline (s) |
|---|---|---|---:|---:|
| matched import baseline | `Baseline` | 1.280, 1.675, 1.682 | 1.675 | - |
| positive random `n = 12` relabelled pair | `Positive12` | 1.606, 1.615, 1.583 | 1.606 | -0.069 |
| negative pair from the two `G(12, 1/2)` seeds | `Negative12` | 1.806, 1.764, 1.787 | 1.787 | +0.112 |
| positive ordered-colour pair at `n = 10` | `Coloured10Pos` | 1.773, 1.776, 1.820 | 1.776 | +0.101 |
| negative ordered-colour pair at `n = 10` | `Coloured10Neg` | 1.661, 1.660, 1.668 | 1.661 | -0.014 |
| scheduled negative CFI pair, `n = 40` | `Cfi` | 33.592, 34.206 | 33.899 | +32.224 |

The baseline's own sample range is 0.402 s, so all four merge-build deltas are
unresolved: at these sizes a `graph_iso` call does not separate from import
noise, which is the honest reading and not evidence of zero cost. The absolute
wall times are the contract, and all four are under 1.9 s. The scheduled CFI
pair resolves decisively at roughly 20x the baseline, which is exactly why it
has its own `HexGraphIsoCfiProbe` Lake target and stays out of the merge build.
`Positive12` and `Coloured10Neg` came in marginally under the baseline median,
which is what an unresolved delta looks like from below.

Breadth for the tactic tier comes from the recorded snapshot
`hexgraphiso-tactic-b4e80b4517b7-chungus2.json` over the 34-instance
`decision-pairs` corpus, under a 120 s wallclock budget and internal caps of
`10 ^ 8` search nodes and `10 ^ 9` checker steps. Thirty-two of 34 solve, with
a geometric mean of 202.83 ms:

| slice | count | range |
|---|---:|---|
| positive | 18 | 19.51 ms (`pos-q3`) to 589.86 ms (`pos-kneser10-2`) |
| negative, solved | 14 | 301.10 ms (`neg-c6-vs-2c3`) to 88.32 s (`neg-circ48-vs-2circ24`) |
| negative, unsolved | 2 | `neg-circ96-vs-2circ48` at `n = 96`, `neg-paley61-vs-circulant61` at `n = 61` |

The asymmetry is the tactic tier's defining shape and it matches the theory: a
positive goal replays a single permutation witness, while a negative goal must
replay enough of the search to establish that no witness exists. Twelve of the
18 positives are under 30 ms; every negative is above 300 ms. The `cycles`
family gives a clean ladder at `n = 6, 8, 10, 12, 14, 16`: 0.301, 0.538, 0.943,
1.416, 2.202, 3.106 s. Both non-solves are negatives, which is the honest
frontier of this tier and is already recorded as such in the SPEC.

One recording caveat: the sweep driver collapses a wallclock timeout and a
non-zero Lean exit into the same `null`, so the two unsolved entries mean "did
not solve within the budget or failed", and this report does not claim which.
A second: the recorded tactic time charges the profiler categories excluding
import, initialization and parsing, so an 88.32 s entry corresponds to a
strictly larger wallclock and is not directly comparable to the 120 s cap.

Timed-region sampling profiles are not part of this report. The compiled
surfaces are microsecond-scale and their cost attribution is already exposed by
the tier decomposition above: `runCertify12` against `runCertReplay12` prices
generation against replay, `runIsIso12` against `runIsIsoChecked12` prices the
checker, and `runHexCanon*` against `runNautyCanon*` prices the Lean-versus-C
constant on identical search trees.

### Kernel cost of the negative routes

`scripts/bench/graphiso_kernel_cost.py` times the `graph_iso` obligation of
each negative corpus pair with the Lean profiler and divides the kernel's
type-checking time by the certificate record count (both sides summed). The
two records below are `hexgraphiso-kernel-7e28eb7ddb6c-chungus2.json` (the
list-state replay, before this work) and
`hexgraphiso-kernel-993d575b06ab-chungus2.json` (the packed replay), both on
this host with a load average near 5.

| pair | n | route | records | kernel s, before | kernel s, after |
|---|---:|---|---:|---:|---:|
| `neg-c6-vs-2c3` | 6 | certs | 23 | 0.315 | 0.083 |
| `neg-c10-vs-2c5` | 10 | certs | 33 | 0.912 | 0.282 |
| `neg-c16-vs-2c8` | 16 | certs | 48 | 3.75 | 1.01 |
| `neg-circulant10-2-5-vs-1-5` | 10 | certs | 26 | 0.892 | 0.204 |
| `neg-kneser72-vs-johnson72` | 21 | certs | 83 | 9.00 | 1.77 |
| `neg-grid4x4-vs-q4` | 16 | root | | 0.769 | 0.202 |
| `neg-grid4x6-vs-2grid3x4` | 24 | root | | 6.17 | 2.21 |
| `neg-paley25-vs-latin5` | 25 | root | | 2.98 | 1.29 |
| `neg-circ48-vs-2circ24` | 48 | certs | 128 | timeout | 64.5 |
| `neg-paley61-vs-circulant61` | 61 | certs | 156 | timeout | 54.3 |

The per-record fit over the eight certificate-route pairs up to 21
vertices moved from `0.50 * n^1.80` ms to `0.29 * n^1.47` ms. Over all ten
certificate-route pairs the fit is `0.054 * n^2.18` ms: the 48- and
61-vertex pairs pay 500 and 350 ms per record, because a refinement pass is
linear in `n` and a node needs up to a pass per cell. The 96-vertex pair
remains out of budget: with `maxRecDepth` raised to 100000 (the default
limit stops the kernel) its 248 records took 377 s of kernel time before
the heartbeat limit.

Where the time went, on the Kneser side at 21 vertices (42 records), from a
`kdecide` probe of the individual definitions:

| stage of the obligation | list-state replay | packed replay |
|---|---:|---:|
| whole side | 3.06 s | 0.54 s |
| tie of the adjacency (the family's own evaluation) | 0.41 s | 0.41 s |
| rows rebuilt from the literal | 0.15 s | 0.02 s |
| automorphism validation (8 generators) | 0.38 s | 0.06 s |
| root refinement | 34 ms | 5 ms |
| one leaf's rows | 52 ms | 6 ms |
| one `popCount` of a 21-bit row | 1 ms | 0.14 ms |

Kernel step prices measured on this host: an accelerated `Nat` operation
about 2 µs whatever the operand size, a bare `Nat.rec` step about 2 µs, a
structural-recursion step on a `Nat` fuel about 8 µs, a `List.range`
element about 20 µs, a `List.map` step about 15 µs, a list read or write at
index `i` about `i` steps. Nesting depth is not the constraint: a chain of
30000 nested `mash` applications evaluated in 0.5 s. The packed replay
follows from these prices: fixed-width fields in one `Nat` for the
labelling, partition and rows (read: a shift and a mask; write: eight
steps), raw `Nat.beq`/`Nat.blt`/`Nat.land` spellings in place of
`if`/`==`/`&&&` (each of those unfolds through eight to fifteen instance
steps), a byte-table `popCount`, and counted loops as one `Nat.rec` step
per iteration.

Carrying more in the certificate (the refinement's cell-split sequence, the
target cell, the leaf's rows) so that the kernel verifies rather than
recomputes was examined against these prices and not adopted. A
refinement pass over packed state is linear in the cell sizes it touches,
and its dominant term is the neighbour count of every member into the
splitter set, which a verifier must compute as well before it can check a
claimed split; the write-back and the window scan the verifier would skip
are under a quarter of a pass, while the certificate would grow by a split
sequence per node. The target cell and the leaf rows cost a few
milliseconds per node and per leaf after packing.

The adjacency tie is the floor the SPEC records: at 21 vertices the Kneser
family's `unrankColex` predicate costs the kernel 0.41 s per side, 45 percent
of the side; for `neg-grid4x6-vs-2grid3x4` the `copies` family reads the
inner graph's stored matrix through `Array` indexing and the tie is over two
seconds of the 2.2 s total. Those are the graph definitions' own kernel
costs, not the replay's.

With `precompileModules` on `HexGraphIso`, the compiled search the tactic
runs at elaboration time runs compiled when the library's shared objects are
loaded: interpretation on the Kneser pair fell from 0.41 s to 0.01 s and on
the 48-vertex pair from 3.4 s to 0.1 s. `lake env lean` does not load them,
`lake lean` and a downstream `lake build` do; the cactus script and the
kernel-cost harness use `lake lean`.

## Concerns

One open item, recorded rather than blocking.

`runDenseConvert` does not validate its declared `n ^ 2` model on this host: the
harness reports inconclusive with `beta = +0.271` and the constant climbing from
25.331 at `n = 32` to 62.960 at `n = 256`. This is a Phase-4 gap for that one
registration, and it is stated as a gap rather than papered over. Two things
make it unlikely to be a defect in the library. The intervening `n = 64` and
`n = 128` rungs were excluded for falling below the per-spawn floor, so the
slope is fitted across a wide gap; and the registration's sink sums `Array Nat`
bitsets whose operands grow with `n`, so the timed region is conversion plus a
GMP summation rather than conversion alone. Resolving it means either raising
`--param-floor` to recover the middle rungs or changing the sink to a
width-independent digest, both of which are bench-driver work in
`bench/HexGraphIso/Bench.lean` and neither of which touches shipped source.

Two measurement caveats stated above rather than here, because they are
properties of the record and not defects: the committed sweep is one
release-plumbing commit behind branch HEAD and must be regenerated before this
branch lands, and the fresh-module probe timings are an unpinned three-sample
run whose null envelope is inferred from the baseline's own spread. The probe
evidence supports the SPEC's release condition, that the four cases close
through the kernel within their logical limits, and the order-of-magnitude
statements made here; it does not support a numeric wallclock requirement, and
none is stated.

Nothing else. The library introduces no `sorry`, no `axiom`, and no
`native_decide`; `scripts/release/check_trust_surface.py` covers it.
