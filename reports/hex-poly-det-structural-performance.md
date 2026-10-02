# Structural symbolic determinant routes

The symbolic `det` dispatcher has generic rational row-factor transport,
direct triangular/zero proofs, and bounded sparse cofactor expansion. These
routes replace the diagnostic prototypes with automatic recognition and
ordinary kernel-checked proofs. They remain part of the opt-in symbolic
interface; this focused sample does not establish family-wide default-on wins.

The rational route certifies an arbitrary extracted numeric matrix, proving
entry and target scalar identities with opaque row expressions. The sparse
route selects a row or column with at most two potentially nonzero entries,
accounts for cofactor signs, and stops at reusable formulas of dimension at
most four. Actual expansion is capped at 64 scalar-product leaves and the
shared proof-node budget. Transposed matrices and selected minors are
identified entrywise. Failed target normalization restores the original goal
and retains the existing polynomial certificate and Mathlib fallback.

## Measurement protocol

The nine fixed inputs are the five original diagnostic cases, followed by the
rational and sparse inputs previously selected near one and ten seconds of
Mathlib tactic-plus-kernel work. Their size labels describe those earlier
profiles, not a claim that their quiet whole builds take exactly those times.

`scripts/bench/det_structural_sweep.py` uses the shared fresh-module runner.
Each input receives six adjacent pairs in alternating AB/BA order, with a
matched import-only baseline per arm. Both arms import the production tactic
and Mathlib's comparator. The comparator remains `simp only [norm_det] <;> ring`.
Timing modules have profiling and certificate tracing disabled and contain no
clock or axiom-printing commands. Separate audit modules verify the generated
proof's route and its axioms. Every completed sample is retained, with host
context, automatically leased CPU, source hashes, and compiler output.

Measurements are serial. Each build has a 60-second ceiling, and the entire
measurement campaign, including diagnostic profiles and setup, has a 30-minute
ceiling. A timeout stops the sweep before any larger input. The preregistered
stop rule for a confirmed loss requires Mathlib to win at least five pairs
and have a median advantage above 200 ms; smaller differences are reported
without treating Lake's completion polling as a precise tactic clock. No
quiet-core selection, sample filtering, or unchanged timing rerun is used.

The older prototype profiles included profiling and axiom-audit overhead in
their whole-build totals. They are not a matched before/after baseline for
these quiet measurements. Results here compare the integrated tactic directly
against Mathlib on identical goals.

## Quiet paired results

Times are median fresh-build differences from the matched import-only baseline,
in seconds. They include statement elaboration and proof checking. They are
not tactic-only clock measurements.

| Input | Probe | Mathlib | `det` | Ratio Mathlib/Hex | Hex pair wins |
|---|---|---:|---:|---:|---:|
| 2×2 integer diagonal | `Diagonal2` | 0.061 | 0.064 | 0.95× | 5/6 |
| 2×2 rational, divided entries | `Rational2` | 0.100 | 0.085 | 1.17× | 4/6 |
| 3×3 integer triangular | `Triangular3` | 0.080 | 0.074 | 1.08× | 4/6 |
| 5×5 integer, independent dense 4×4 block | `Independent5` | 0.296 | 0.199 | 1.49× | 6/6 |
| 3×3 rational, five-term quadratic row factors | `RationalFive3` | 0.592 | 0.398 | 1.49× | 6/6 |
| 3×3 rational, eight-term quadratic row factors | `RationalOne` | 1.594 | 0.638 | 2.50× | 6/6 |
| 5×5 integer, sparse block with two-term entries | `SparseOne` | 2.481 | 0.905 | 2.74× | 6/6 |
| 3×3 rational, twelve-term quartic row factors | `RationalTen` | 12.875 | 3.379 | 3.81× | 6/6 |
| 5×5 integer, sparse block with two/three-term entries | `SparseTen` | 22.736 | 7.636 | 2.98× | 6/6 |

The three smallest differences are inconclusive at this measurement resolution.
The six larger examples favor Hex in every completed pair. These are focused
structural examples, not a representative sample of all symbolic determinants.

## Representative attribution

One separate instrumented comparison per changed family follows. The tactic
clock includes synchronous auxiliary checking; the final theorem kernel counter
is added once. These diagnostic samples are not the six-pair medians above.

| Input | Arm | Tactic ms | Final kernel ms | Sum ms |
|---|---|---:|---:|---:|
| `Triangular3` | Mathlib | 16.20 | 7.05 | 23.25 |
| `Triangular3` | Hex | 12.57 | 0.21 | 12.77 |
| `RationalOne` | Mathlib | 458.96 | 494.00 | 952.96 |
| `RationalOne` | Hex | 172.23 | 0.36 | 172.59 |
| `SparseOne` | Mathlib | 740.83 | 489.00 | 1229.83 |
| `SparseOne` | Hex | 267.67 | 164.00 | 431.67 |

## Retained data and validation

The [raw archive](bench-results/hex-det-tree/structural/) contains all completed
and interrupted observations, compiler output, source snapshots, host context,
and run status. The measured production implementation is commit
`49d235714`. Its source-hash manifest was recorded separately from the
runner and matches that commit. Each retained directory includes the actual
script used there; the current runner writes the manifest itself before a run.
The final validation below records the additional operation admission checks
and configurable structural proof budget in commit `a3772fce9`.

The initial audit parser required a multiline-output fix before any paired
measurement. In the main run, the first large sparse candidate received
SIGTERM after 7.52 seconds; this was not a timeout, and its cause is unknown.
Its proof audit and the preceding Mathlib measurement completed. A single
bounded recovery reused source-verified audits and collected six fresh adjacent
pairs. The orphan Mathlib sample remains in the archive but is not paired with
a later Hex sample across the interruption. No completed pair was replaced.

The aggregate measurement time, including setup, recovery, profiles, and final checks, was
**25.95 minutes** against the 30-minute ceiling. Builds were serial,
limited to 60 seconds each, without memory caps. These are manual Mathlib-facing
proof probes; no Mathlib-importing executable benchmark was registered.

Validation passed: full `lake build`, determinant kernel tests, unchanged
conformance fixtures, 42 exact oracle records, DAG and Phase-4 checks, release
manifest validation, the Mathlib-free benchmark guard, and seven resource-limit
harness tests. Every accepted audit uses only `propext`, `Classical.choice`,
and `Quot.sound`. Route audits confirm the intended integrated dispatch.

The original general tree-certificate assembly, entry/target kernel-time,
and proof-size targets in issue #10320 remain separate obligations. This
focused structural evidence does not establish those targets or justify
changing the family-wide opt-in decision.

A failed structural target comparison can be more expensive than a successful
one: it then attempts the polynomial certificate and Mathlib fallback. The
60-second probe ceiling is an external operational limit, not a new tactic
heartbeat policy. All structural regression examples, including two cofactor
branches and two expansion levels in dimension six, compile under Lean's
default heartbeat limit.

## Final admission and budget checks

Commit `a3772fce9` authenticates rational operation instances and operand types
before numeric certification and threads the shared proof budget through the
structural route. A final six-pair comparison covers one input per changed
family, with fresh route/axiom audits and the same quiet protocol.

| Input | Mathlib seconds | `det` seconds | Hex pair wins |
|---|---:|---:|---:|
| `Triangular3` | 0.026 | 0.019 | 4/6 |
| `RationalOne` | 1.619 | 0.600 | 6/6 |
| `SparseOne` | 2.305 | 0.832 | 6/6 |

The tiny triangular comparison remains inconclusive. Both larger comparisons
still favor Hex in all six pairs. The initial nine-case table remains intact;
these changed-code observations do not replace any earlier samples. The final
runner itself records the source manifest before measurement.
