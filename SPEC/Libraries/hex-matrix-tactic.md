# hex-matrix-tactic

Proof-producing `det`, `rank`, and `char_poly` frontends for executable Hex
matrices. The [Mathlib companion](hex-matrix-tactic-mathlib.md) accepts
Mathlib matrices and integrates with `norm_det` and `norm_rank`. These are
independent tactics with plain names; duplicating a Mathlib tactic is allowed.
The performance objective is a measured, reproducible speedup on named
families, with slower cases driving optimisation. Benchmarking determines
strategy and documents coverage; it does not decide whether a tactic may ship.

This SPEC specifies future implementation, not an implemented API. It follows
[the matrix design in PR #9437](https://github.com/kim-em/hex-dev/pull/9437),
with numeric support independent of the separately specified
[hex-reflect](hex-reflect.md).

## Boundary and dependencies

`HexMatrixTactic` owns Hex literal recognition, entry-model selection, matrix
batch conversion, algorithm selection, result reconstruction, and syntax.
It accepts `Hex.Matrix R n m`, with concrete natural dimensions, through the
public `ofFn`, `ofRows`, row and entry APIs and the library's notation. It
must not access the private backing buffer or recognize Mathlib syntax.

Its direct dependencies are `HexMatrix`, `HexBareiss`, `HexRowReduce`,
`HexCharPoly`, and the planned `HexRank`. `HexDeterminant`, `HexPoly`,
`HexArith`, and `HexBasic` are available transitively. It imports Lean's
elaborator API, but no Mathlib. The companion sits above this library and the
corresponding Mathlib bridges. Neither numeric library imports `HexReflect`
or `HexReflectMathlib`.

The `libraries.yml` entries are `status: planned`, `done_through: 0`, with no
Lake targets or umbrella files until activation. These edges follow
`scripts/check_dag.py` and its `libgraph.may_import` dependency closure.
The existing lower libraries must never import either frontend. Symbolic
integration will live in a separately registered downstream library depending
on both this frontend and reflection (and their companions where needed).
It cannot be an optional file in the numeric library whose import would
silently expand that library's dependency closure.

## Entry models and conversion

A computation model mirrors `Mathlib.Tactic.Echelon.BareissExt`: a Meta-level
lookup on the carrier returns a producer or declines. The executable value
type, arithmetic, preparation/restoration and quotation are separate pieces.
A model records zero, one, multiplication, subtraction, a zero test and,
when available, an exact quotient. It also supplies the addition and
interpretation laws needed by Hex algorithms. Preparation converts a whole
matrix, retaining dimensions, row-major order, original entry expressions,
and one proof of each entry's interpretation. Restoration accounts for every
row scale or coefficient conversion, not just the returned scalar.

Lookup and caches include the exact carrier, algebraic instances,
interpretation map, configuration and, for symbolic input, sealed variable
environment. Matching only a type name is insufficient. Discovery and
quotation are untrusted; an executable zero test is not a proof of its answer.

| Entry model | Accepted fragment and proof obligation |
|---|---|
| Closed `Int`, `Rat` | Kernel-transparent arithmetic and equality; rational denominators are nonzero and any denominator clearing has a proved restoration. |
| Closed `ZMod n`, `Fin n` | Literal modulus, kernel-decidable equality and lawful ring operations. `ZMod` recognition belongs in the companion; `Fin n` requires positive `n` for its modular ring. Determinant and characteristic polynomial allow composite moduli; rank requires a domain/field model, normally prime modulus, and cannot assume primality. `ZMod 0` follows its integer model. |
| Literals in `ℝ`, `ℂ` | The companion proves entries equal to images of computable values using `norm_num` and registered interpretation lemmas. Rational-valued literals use `Rat`; complex literals involving `I` need an explicit computable extension. Never run kernel equality on classical real or complex instances. |
| Closed algebraic entries | A registered computable number-field or real-algebraic carrier and certified embedding, with nonzero preservation for rank. This is a numeric provider extension, independent of symbolic reflection. |
| Symbolic entries | A later `hex-reflect` provider converts the entire matrix in one batch, seals variables once and supplies interpretation equalities. Intermediate polynomial matrices are not printed and reparsed. |

Determinant and characteristic polynomial commute with a ring homomorphism;
rank additionally needs injectivity or explicit proofs that the chosen minor
remains nonzero under interpretation. A symbolic polynomial nonzero before
specialization may become zero afterwards. Generic rank must name the
polynomial domain or its fraction field; conditional specialized rank retains
all nonvanishing conditions. Unconditional rank of arbitrary specializations
is not promised. Piecewise rank and case splitting are later work.

## Frontends and results

The term forms `det A`, `rank A`, and `char_poly A` return dependent records
with fields `value` and `proof`, the latter asserting that the requested
operation on the original matrix equals `value`. Determinant values are in
the source carrier, rank values in `Nat`, and characteristic-polynomial
values in `Hex.DensePoly R` or the companion's `Polynomial R`.

The goal forms close determinant equality, rank equality or either inequality,
and characteristic-polynomial equality. On Hex inputs these refer to the
selected executable determinant, field rank or explicitly interpreted integer
rank, and `Hex.Matrix.charPoly`; the companion gives the exact Mathlib
statements. Square shape is required for determinant and characteristic
polynomial; rank supports rectangular and empty matrices. Empty square
matrices have determinant `1`, rank `0`, and characteristic polynomial `1`.

An equality tactic checks the requested right-hand side against the certified
result, including coefficientwise polynomial equality. Rank inequalities use
the certified equality followed by a checked natural-number comparison; a
one-sided minor or spanning certificate may avoid computing the opposite bound
when its soundness theorem suffices. A false target remains unproved.

The common internal protocol distinguishes `notApplicable` (wrong fragment),
`declined` (unsupported capability or exhausted budget), `success` (value and
proof, or explicitly conditional result), and `failure` (malformed output or
failed certificate). A tactic closes a goal only after every condition is
proved. Programmatic conditional results expose an ordered condition list and
a proof depending on it; unconditional term forms decline unresolved
conditions. Diagnostics identify the operation, carrier, entry coordinate,
missing capability or exceeded budget. No failure substitutes a weaker goal.

## Algorithms and proof strategy

Initial determinant selection is:

| Input and laws | Producer |
|---|---|
| Closed `Int` | Row-pivoted fraction-free Bareiss |
| Closed field with certified exact quotient | Bareiss, with denominator restoration when working integrally |
| Commutative ring without exact quotient | Samuelson–Berkowitz, returning `(-1)^n` times the constant coefficient of `det(X I - A)` |
| Symbolic polynomial entries with certified exact quotient | Polynomial Bareiss |
| Symbolic polynomial entries without exact quotient | Samuelson–Berkowitz with the same sign correction |

Characteristic polynomial uses Samuelson–Berkowitz. The characteristic
variable stays separate from reflected entry variables, for example in
`DensePoly (MvPoly k C cmp)`. Rank uses verified field row reduction or the
two-sided domain certificate and fraction-free producer specified by
[hex-rank](hex-rank.md). That certificate and its companion's soundness are
planned dependencies, not existing declarations.

There are two proof strategies:

- **Transport and kernel evaluation.** Materialize a Hex input, transport by
  correspondence, then prove a closed executable equality by kernel `decide`
  (`Lean.Meta.mkDecideProof`, or `decide +kernel` in source examples).
  For Bareiss the equality must mention `bareiss`/`bareissWith`; reducing
  `Hex.Matrix.det` instead evaluates its Leibniz definition. Either way,
  evaluating a producer equality in the kernel replays that producer.
- **Certificates.** Compiled code proposes intermediate values; kernel checks
  local equations or a smaller result certificate, and a soundness theorem
  yields the result. Keep the existing Berkowitz certificate path. Rank's
  nonzero minor and column-expression certificate can check in `O(n m r)`
  arithmetic operations at fixed rank, avoiding full elimination. Determinant
  step certificates still verify elimination arithmetic: no generally cheaper
  determinant certificate is assumed.

Selection is provisional until Phase 4 measures it. Record dimensions and
rank, maximum coefficient numerator/denominator bit lengths, estimated minor
bit growth, and predicted certificate size. For symbolic matrices also record
variable count, degree, support and intermediate support growth. Small
matrices with bounded coefficients initially use direct replay; larger
coefficients, costly kernel division or repeated polynomial expansion favour
local checks; low-rank inputs favour the two-sided certificate. Dimension
alone is never a cutoff. Model-specific thresholds, proof-size and search
budgets are fixed from the benchmark tables before claiming Phase 4 and
reported with the chosen strategy. Provide a diagnostic strategy override for
matched measurements and reproducibility.

## Trust and migration

No `native_decide`, new axioms or trusted runtime verdicts. Kernel `decide`
proves transparent entry equalities, finite shape/index checks, arithmetic
leaves, Boolean checker acceptance and direct producer equalities. Certificate
soundness theorems prove the advertised operation from those checks.
Transport lemmas prove input reconstruction, operation correspondence and
coefficient interpretation. Noncomputable-source equalities use proved
normalization and interpretation, never evaluation of classical equality.
Audit accepted theorem axiom sets for unexpected dependencies.

Move the frontend machinery from `HexCharPoly/CharPolyElab.lean` into this
library, and its Mathlib literal enumeration, `RowCertificate` /
`MatrixCertificate` construction and RHS recognition from
`HexCharPolyMathlib/CharPolyElab.lean` into the companion's shared conversion
layer. Keep `Hex.Matrix.charPoly`, Berkowitz computation, its local certificate
checks and soundness, and `HexCharPolyMathlib.equiv_charPoly` in their owning
algorithm libraries. Generalize or reuse those checks rather than replacing
them by full kernel recomputation. Numeric polynomial reconstruction remains
available without reflection; the symbolic adapter later supplies shared
polynomial normalization instead of the bespoke structural matcher.

Current result fields are `poly` and `charPoly_eq`, not literally `value` and
`proof`. Preserve compatibility projections and the existing goal/term forms
while introducing the uniform records. Compatibility imports must be
restructured without a lower-library import of `HexMatrixTactic`: an old
frontend import may need migration to the new umbrella. Importing both
umbrellas must register each syntax handler only once.

## Phase-4 evidence

Follow [benchmarking](../benchmarking.md), especially fresh-module proof
evidence and the headline report format. Reports are
`reports/hex-matrix-tactic-performance.md` and
`reports/hex-matrix-tactic-mathlib-performance.md`, with **Bench targets**,
**Verdicts**, **Comparator ratios**, **Profile**, and **Concerns**
sections. The companion owns its Mathlib proof probes; it is not a
correspondence-only layer because it implements frontends and adapters.

**Fixtures.** Commit deterministic seeds, exact entries, dimensions, expected
results and hashes in `conformance-fixtures/HexMatrixTactic/matrices.jsonl`;
companion notation/interpretation cases live in
`conformance-fixtures/HexMatrixTacticMathlib/literals.jsonl`. Use these named
families, also in the Phase-4 tables:

| Family | Parameter ladder and purpose |
|---|---|
| `dense` | Seeded full-rank square `Int` matrices, dimensions `2,4,8,16,32`, entry bits `8,32`; rational variants with denominator bits `4,16`. |
| `structured` | Tridiagonal and Vandermonde matrices on the same dimension ladder; include required pivot swaps. |
| `singular` | Duplicate rows and products of certified rank `n-1`, including a late failed pivot, on that ladder. |
| `low-rank` | Products of `n × r` and `r × m` factors with a known nonsingular `r`-minor, `n,m = 8,16,32,64`, `r = 1,2,4`; include nonleading pivot columns and rectangular shapes. |
| `large-coefficients` | Dense and rank-2 inputs, dimensions `2,4,8,16`, entry bits `64,256,1024`; record intermediate bit lengths. |
| `finite-carriers` | Corresponding small matrices over `ZMod 7`, `Fin 7`, and composite modulus `8`; composite cases test only determinant and characteristic polynomial. |
| `closed-algebraic` | Blocks `[[α,1],[1,α]]` with `α²=2`, and block-coupled variants, dimensions `2,4,8,16`; see companion for exact embeddings and comparator obligations. |
| `symbolic` (later) | Dimensions `2,4,8`, variables `1,2,4,8`, degree `1,2,4`, support `1,4,16`; include repeated subexpressions, generic full rank and known low rank. Record realized support, not just generation limits. |

**Compiled registrations.** `bench/HexMatrixTactic/Bench.lean` remains
Mathlib-free. Register producer, certificate construction and checker
separately; checker preparation holds a precomputed certificate. Reuse the
underlying libraries' complexity claims on identical families and parameters;
frontend-specific irregular fixed workloads use mode 3 with a preregistered
comparator-anchored ceiling, explaining why modes 1 and 2 do not apply. Do not
claim one cubic time model across bit-size and symbolic-support ladders.

**Proof probes.** Reserve `bench/HexMatrixTactic/ProofProbe` and
`bench/HexMatrixTacticMathlib/ProofProbe` in each owner's `proof_probes` metadata.
Use external fresh `lake build +<module>:olean` runs with warm dependencies,
matched import-only and construction-only baselines, and variants for entry
conversion, producer-only search, certificate construction, literal emission,
replay and full elaboration. Separate construction from producer discovery;
report matched differences as attribution estimates, not additive exact
clocks. No clocks, timing loops, executables or LeanBench imports inside
probes. Record producer time, certificate construction, kernel checking,
proof-expression node count/serialized bytes, `.olean` size, and total
elaboration separately. Include one representative compiled profile per declared numeric input family;
proof-track attribution uses the matched builds above.

**Comparators.** In the companion, unmodified pinned `norm_det`/`eval_det` and
`norm_rank`/`eval_rank` are gating comparators: wiring, coverage and reported
ratios are mandatory. Run them without the Hex extensions imported, alongside
separate Hex-enabled adapter arms. Hex's current `char_poly` is the
characteristic-polynomial regression comparator; no nonexistent Mathlib
`norm_char_poly` is assumed. Compare identical literal inputs and targets;
report additional notation conversion separately. Unsupported comparator
fragments are recorded with the diagnostic and a matched supported subfamily,
never fabricated timings.

**Required checks and ceilings.** The external proof-runner manifest records
these fixed smoke/regression obligations before measurement; they are
operational limits, not portable scientific budgets:

| Check | Canonical input | Ceiling / required result |
|---|---|---|
| `literal-roundtrip` | All four Mathlib syntaxes, `0 × 0`, `0 × 3`, `3 × 0`, and `2 × 2` | Exact shape and entry proofs; reject transposed/incorrect entries. |
| `numeric-proof` | `dense` dimension 4, 8-bit entries, each operation and rank inequality | Full proof-build median ≤ 10 s per case; theorem axiom audit passes. |
| `large-proof` | `large-coefficients` dimension 4, 256-bit entries | Full proof-build median ≤ 30 s per case; serialized proof ≤ 32 MiB. |
| `certificate-rejection` | Wrong value, changed pivot/minor/column coefficient, wrong size or modulus | Rejection without a theorem; median ≤ 10 s per case. |
| `algebraic-proof` | One `α²=2` block and rational literals in `ℝ`, `ℂ` | Kernel-checked transported result, median ≤ 30 s per case. |
| `bench-verify` | Smallest rung of each compiled registration | Per-library `Bench verify` 30 s soft warning; stay within the existing combined hard cap and extend the existing script only. |

Every fresh build has a 120 s cleanup timeout; timeout or incomplete pair
invalidates that evidence. Scheduled larger rungs retain timeouts as outcomes
and cannot be reported as passing samples. Recalibrate fixed ceilings only
with documented evidence, not merely to make a failure pass. Keep required
CI checks small; timing-sensitive scientific runs are manual on the shared
host, with no extra CI jobs or workflows.

Collect an even preregistered number of rounds (initially eight), adjacent
comparator/Hex pairs, alternating AB/BA. Retain every completed sample,
record host load, and automatically select one CPU when supported. Do not
wait for quiet or reject busy-host samples; allow at most one unchanged
rerun after inconclusive evidence. Record pristine commit and source hashes,
toolchain and Mathlib pin, commands, options, seeds, CPU/OS, all raw timings,
paired deltas and the exact strategy decision.

The Phase-4 target is a reproducible total-elaboration speedup over **each**
of `norm_det` and `norm_rank` on explicitly named families and eligible
rungs, with a resolved paired effect rather than a universal speed claim.
Tables contain every shared rung and list the selected strategy, each phase,
proof size, both totals, ratio and uncertainty. Set a numerical improvement
target from the baseline before optimisation; do not select only winning
samples. If there is no measured win yet, report the unmet target and planned
optimisation rather than prohibiting the frontend. Slower cases name evidence
for the cause and a remedy: kernel elimination replay → local arithmetic
certificates or a different producer; rank multiplication cost → the smaller
minor/column certificate or blocked checks; certificate size → shared literals
and coarser checked blocks; elaboration overhead → shared entry conversion and
proof caches; symbolic expansion → certified exact quotients or representation
changes. Revise the provisional strategy table from these measurements.
