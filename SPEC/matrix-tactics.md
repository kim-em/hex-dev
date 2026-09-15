# Matrix tactics

Proof-producing tactics on closed matrices (`rank`, `det`, `char_poly`, and
later `min_poly`, `smith`, `hermite`, `inverse`, `solve`) are not a library of their own. Each
tactic lives with the algorithm library whose certificate it checks, its
Mathlib-input form lives in that library's Mathlib companion, and the only
shared code is the literal layer of `hex-matrix-mathlib`. This note fixes
that placement, the certificate discipline that makes a tactic fast in the
kernel, the bar every tactic must clear against the pinned Mathlib tactic
before it ships, and the measured record of the designs that failed that
bar, so that the next attempt is strictly better in runtime and in scope.

It replaces the withdrawn `hex-matrix-tactic` and `hex-matrix-tactic-mathlib`
library SPECs (closed in https://github.com/kim-em/hex-dev/pull/10204, "feat(matrix-tactic): activate the det, rank and char_poly frontends"). Their
fixture families, outcome protocol and syntax conventions survive below;
their library structure and their kernel-replay proof strategy do not.

## Placement

| tactic | goals | executable side | Mathlib-input tactic and soundness | status |
|---|---|---|---|---|
| `rank` | `A.rank = r`, `A.rank ≤ r`, `r ≤ A.rank` | `hex-rank`: `RankWitness`, `checkRankList`, `rankWitness` | `hex-rank-mathlib`: `rank_eq_of_checkList`, `HexRankMathlib/Tactic.lean` | shipped (https://github.com/kim-em/hex-dev/pull/10207) |
| `det` | `A.det = d` | `hex-bareiss`: `DetWitness`, `checkDetList`, `checkDetRat`, `detWitness` | `hex-bareiss-mathlib`: `det_eq_of_checkList`, `det_eq_of_checkRat`, `HexBareissMathlib/Tactic.lean` (`det`, `det%`, `Hex.norm_det`, renamed from `hex_norm_det`) | shipped (https://github.com/kim-em/hex-dev/pull/10224); see [The determinant certificate](#the-determinant-certificate) |
| `char_poly` | `A.charpoly = p` | `hex-char-poly`: the Berkowitz certificate, in kernel form | `hex-char-poly-mathlib` | packed list certificate and both frontends in `HexCharPoly`/`HexCharPolyMathlib`; measurements in `HexCharPolyMathlib/SPEC/hex-char-poly-mathlib.md` |
| `rank`, symbolic entries | `A.rank = r` (conditional), `A.rank ≤ r`, generic rank of the reified matrix | `hex-generic-rank`: hex-rank's certificate at `MvPoly` | `hex-generic-rank-mathlib`: a second handler on the `rank` syntax kind; `checkRank_sound_at` | implemented: [hex-generic-rank-mathlib](../HexGenericRankMathlib/SPEC/hex-generic-rank-mathlib.md) |
| `det`, symbolic entries | `A.det = e`, `e = A.det`, `det% A` (unconditional; any commutative ring; closed forms for `n ≤ 3`) | `hex-bareiss`: generic `detWitness`, `checkDetPolyList`; `hex-poly-det`: the `MvPoly` instantiation | `hex-poly-det-mathlib`: `checkDetPolyList_sound`, second handler on the `det` syntax kind, opt-in `Hex.normPolyDet` | specified: [hex-poly-det-mathlib](Libraries/hex-poly-det-mathlib.md); relocated out of the published hex-bareiss-mathlib |
| `kronecker` | `a = b` for characteristic-zero commutative-ring expressions | `hex-kronecker`: `Expr`, `checkExprEq`; quotient-witness checks are programmatic only | `hex-kronecker-mathlib`: `checkExprEq_sound`, `kronecker`, `kronecker%` | planned, explicitly opt-in: [hex-kronecker-mathlib](Libraries/hex-kronecker-mathlib.md) |
| `rank_locus` | `A.rank < r ↔ ⋀ gᵢ = 0` as a hypothesis; `A.rank < r`, `A.rank ≤ r`, `r ≤ A.rank`, `A.rank = r` | `hex-determinantal-ideal`: `detIdealGens`, and its list form `detIdealGensList` | `hex-determinantal-ideal-mathlib`: `gens_vanish_iff_rank_lt`, `HexDeterminantalIdealMathlib/Tactic.lean`; default `r` from a hex-generic-rank-mathlib handler | specified: [hex-determinantal-ideal-mathlib §The `rank_locus` tactic](../HexDeterminantalIdealMathlib/SPEC/hex-determinantal-ideal-mathlib.md#the-rank_locus-tactic) |
| `min_poly` | `minpoly F A = p` | hex-min-poly: list form of `MinPolyCert` | hex-min-poly-mathlib | implemented in `HexMinPolyMathlib/Tactic.lean`: [companion contract](../HexMinPolyMathlib/SPEC/hex-min-poly-mathlib.md#the-min_poly-tactic) |
| `smith` | integer row-presentation quotient equivalence | hex-smith: list form of `snfCert` | hex-smith-mathlib; optional polynomial handler in hex-poly-smith-mathlib | implemented in `HexSmithMathlib/Tactic.lean`: [companion contract](../HexSmithMathlib/SPEC/hex-smith-mathlib.md#the-smith-tactic) |
| `hermite` | integer lattice membership and row-lattice basis | hex-hermite: list form of `hnfCert` and checked remainder | hex-hermite-mathlib | implemented in `HexHermiteMathlib/Tactic.lean`: [companion contract](../HexHermiteMathlib/SPEC/hex-hermite-mathlib.md#the-hermite-tactic) |
| `inverse` | `A * B = 1`, `A⁻¹ = B` | hex-row-reduce: list products or nonzero kernel vector | hex-row-reduce-mathlib | specified: [companion contract](../HexRowReduceMathlib/SPEC/hex-row-reduce-mathlib.md#the-inverse-tactic) |
| `solve` | `A.mulVec x = b`, existence or inconsistency | hex-row-reduce: list residual, complete RREF data or separator | hex-row-reduce-mathlib | specified: [companion contract](../HexRowReduceMathlib/SPEC/hex-row-reduce-mathlib.md#the-solve-tactic) |
| literal layer | reading `!![…]`, `Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray xs h` | none | `hex-matrix-mathlib`: `ofLists`, `vecOfList`, `entriesEq`, literal recognition, definitional identification (`HexMatrixMathlib/Literal.lean`) | shipped (https://github.com/kim-em/hex-dev/pull/10218) |

`invariant_factors` is reserved for hex-invariant-factors; it is not an alias
for `smith`. The five structural frontends use the
absolute-budget proof track in their companion contracts because Mathlib has
no dedicated tactic for those results. Ordinary entrywise normalization is
an informational baseline for inverse-product and supplied-solution goals.

Rules that follow from the table:

- No library is named for being a tactic. A tactic is a frontend to one
  certificate, and it lives where that certificate's soundness theorem
  lives; a second tactic for the same operation is not added beside the
  first.
- The tactic keyword is declared once, by the owning library, as a
  non-reserved atom (`syntax (name := rankTac) &"rank" : tactic`), so
  `rank` and `det` remain ordinary identifiers and function applications
  everywhere. A library that later wants to handle more inputs under the
  same keyword attaches a `@[tactic]` handler to the owner's syntax kind and
  answers `throwUnsupportedSyntax` outside its fragment; it does not
  redeclare the keyword. The result-producing term forms use `%`
  (`det% A`) to stay clear of the function applications `det A`.
- Goals on `Hex.Matrix` inputs (`Hex.Matrix.bareiss A = d`,
  `Hex.Matrix.rank A = r`) are a separate obligation of each owning
  library, not a reason for a shared frontend, and they carry the same
  kernel and measurement discipline as the Mathlib forms. They need a
  Mathlib-free soundness theory for the certificate, which `hex-rank` does
  not have today; they are deferred until that exists.
- Symbolic entries are a separate handler on the owner's syntax kind,
  living with the `MvPoly` instantiation of the certificate; a numeric
  handler reports `notApplicable` for them. For `rank` that handler is specified in
  [hex-generic-rank-mathlib](../HexGenericRankMathlib/SPEC/hex-generic-rank-mathlib.md), with
  the three outputs (generic, conditional, locus) that a symbolic rank may
  take. Until a symbolic handler exists for an operation, a Mathlib tactic
  that also handles symbolic input (`norm_det`) is composed as the fallback
  of the Hex tactic in one explicit simp set, so no input that Mathlib
  accepts today regresses.

## Outcome protocol and diagnostics

Every tactic classifies its attempt as `notApplicable` (the goal is not the
operation, or the input is not in the fragment; the next handler may try),
`declined` (in the fragment, but a capability is missing or a budget is
exceeded; the message names the missing capability, carrier, entry
coordinate or budget), `success` (a value and a proof), or `failure` (a
producer bug or a certificate the kernel rejects). A false target is
reported with the certified value before any proof is built. No failure
substitutes a weaker goal. Accepted theorems depend on `propext`,
`Classical.choice` and `Quot.sound` only, and each tactic's tests audit
that axiom set.

For numeric `rank` and `det`, classification precedes entry evaluation and
certificate production. A goal outside the supported comparisons, an open
matrix or bound (including unresolved metavariables), an unrecognized
literal, or a carrier outside the numeric fragment (`ℤ` for `rank`, `ℤ`
and `ℚ` for `det`) is `notApplicable`. The numeric handler throws
`throwUnsupportedSyntax` for these cases. Entry evaluation, producer,
false-target, certificate and budget errors retain their existing diagnostics;
they are not reclassified as unsupported syntax. The literal recognizer
only searches within its fixed unfolding window; not finding a literal
within that window is `notApplicable`, as for any unrecognized expression.
This is distinct from an execution-budget exception, which propagates.

Both numeric handlers have `@[no_fallback]`: in the pinned Lean, ordinary
tactic errors otherwise also try the next handler and a last-resort error
can mask a numeric failure. `throwUnsupportedSyntax` delegates even with
this attribute. Each owning library registers its diagnostic handler first,
then its numeric handler, because Lean tries equal-priority handlers in
reverse registration order. An extension registered later is tried before
these two. Extensions must also have `@[no_fallback]` to preserve their
in-fragment errors, and answer `throwUnsupportedSyntax` outside their
fragment; otherwise the last diagnostic handler can mask an extension error.
The diagnostic handler reclassifies and reports `rank: not applicable: …`
or `det: not applicable: …` when no handler accepts. For determinant
equations, the last-resort handler first tries `simp only [Hex.norm_det]`,
preserving Mathlib's symbolic and other-carrier normalization. The numeric
`det` handler also retains that simp fallback for an in-fragment capability
decline. Errors raised during simp, including producer failures and rejected
certificates, propagate unchanged; only a no-progress result is replaced
with the classification or capability diagnostic.

Regression tests register a stub and then locally re-register the numeric
handler, assert their dispatch order, and exercise both delegation and
committed numeric errors. A later stub alone would run first and would not
test numeric delegation.

The tactics are configured only through the shared structure
`HexMatrixMathlib.KernelConfig`, taken as an `optConfig` in the style of
`decide +kernel` (`rank -packing`, `det -packing`), never through options:
`packing` (default on) selects the Kronecker-packed evaluation of the
certificate's dot products, a second checker proven equal to the plain one
under bounds it verifies, and off gives the plain checker, so the plain
certificate stays measurable and is what a comparison with another
system's certificate refers to.

The proof is added as one auxiliary lemma on the closed target
(`HexMatrixMathlib.Literal.addClosedProof`: `mkAuxLemma` with
asynchronous checking off and no reuse of an earlier lemma for the same
statement, the declaration-checking path `decide +kernel` uses), so the
kernel checks every supplied certificate synchronously and exactly once
and the tactic sees a rejection and can diagnose it (false target,
producer bug, or an entry the kernel cannot reduce). The elaborator
evaluates nothing before the kernel does: neither a `Kernel.whnf`
pre-evaluation of the check nor the `Meta.check` of the proof that
`mkAuxTheorem`'s closure step performs under its default
`zetaDelta := false`; either evaluates the certificate a second time.

The closed-entry `rank` handlers support integers, rationals and
`Zsqrtd d` with an integral-domain instance through `HexRankMathlib`.
`HexRankMathlib.NumberFieldTactic` additionally supports `QAdjoin a` and
checked `PolyQuot p x` presentations, including rational coordinates.
The latter import is optional; the ordinary rank frontend does not load
the number-field bridge. The `closed-algebraic` fixture is the block
`[[α, 1], [1, α]]` with `α² = 2`.

## Kernel discipline

Design principle 11, as `hex-rank` made it concrete: everything on the
kernel's path is a list of `Nat` or `Int`, read by structural recursion,
with arithmetic through `Nat.mul`, `Nat.add`, `Nat.mod`, `Int.mul`,
`Int.add` and comparisons through `Nat.beq`, `Nat.blt` and `Int.decEq`.
Polynomial quotient certificates use coefficient lists and explicit
polynomial-division witnesses, so checking does not divide polynomials.
They require a nontrivial modular quotient, proved from a positive-degree
monic normalization, without a primality or irreducibility test. Rational
row scaling and number-field entry identification are separate linear-size
checks; they may reduce the executable carrier once per matrix entry.
No `Array`, `Vector`, `Fin`, `Finset`, `Hex.Matrix`, `Matrix.of`, `dite`
or well-founded recursion appears on the path, every definition on it is
`@[expose]`, and a Mathlib literal is identified with its row list
definitionally (`vecOfList (k + 1) (a :: l)` unfolds to
`vecCons a (vecOfList k l)`, so `!![…] = ofLists n m L` is `rfl`), never
by evaluating `A i j` through `Matrix.of` inside the arithmetic.

Polynomial certificates have two complementary kernel forms.  The sparse
form is hex-mv-poly's canonical `PolyList`, with coefficientwise list
arithmetic.  The dense-box form is
[hex-kronecker](Libraries/hex-kronecker.md): an unnormalized ring-expression
tree or a supplied `PolyList Int` is evaluated at mixed-radix powers of one
power-of-two base, and balanced-digit injectivity turns one packed integer
comparison back into a polynomial identity.  Polynomial-matrix products use
the existing direct list dot product by default and may reuse
`Hex.Matrix.Packed`'s nonnegative/nonpositive signed packing as a separately
benchmarked outer mode.  Bounds in both dense digits and packed bits are
checked before packing, so consumers select the dense form only when its box
is smaller than their budget and retain term lists otherwise.  Characteristic
`p` never uses base-`p` packed arithmetic: it supplies an integer quotient
witness for `L̃ - R̃ = p Q`, or falls back to the residue term-list checker.
Neither form normalizes a reflected tree on the kernel path.

The loops that run once per multiply-add in the integer rank and
determinant checkers (the dot products `dotNat` and `dotInt` of
`Hex.Matrix.Packed`, and `scaleRow` and `addScaled` of the rank upper
bound) apply `List.rec` directly instead of recursive equations elaborated
through `List.brecOn`, whose `below` tuple the kernel builds and projects
at every step. Such a definition is `noncomputable`, which only suppresses
its compilation, and its equation form is attached by a proven `@[csimp]`
theorem so that the compiled code is the ordinary recursion; this adds no
trusted implementation override (no `implemented_by`). The rewrite
reduced the plain rank check's kernel time by about a third on the
`40 × 40` full-rank bench matrix and the plain determinant check's by a
sixth. Loops that run once per entry or per row, the Hermite and Smith
list dot product (`HexMatrix/Lists.lean`) and the polynomial coefficient
loops keep the equation form.

Two things a certificate must never ask the kernel to do:

- **Replay the producer.** Evaluating `bareissWith`, `rowReduceWith` or
  `charPoly` on the matrix, or their `ofFn`-structured restatements, makes
  the kernel traverse `Vector` buffers, rebuild `ofFn` matrices at every
  access and run the elimination's search and divisions. This is what the
  withdrawn `det` did (`bareissReplay`), and it lost to `eval_det` by a
  factor of three per check ([Measured record](#measured-record)).
- **Check a matrix identity stated on `Hex.Matrix`.** `checkRank` on a
  precomputed `RankCert` takes 371 s at `16 × 16` where `checkRankList`
  takes 115 ms on the same data. The reference checker stays the form the
  proofs use; the kernel gets its own.

Producers stay in the executable libraries and are unchanged by this: the
kernel form is a reshaping of the same certificate data, produced from the
reference certificate (`rankWitness` from `rankCert`).

## The determinant certificate

For `A : Matrix (Fin n) (Fin n) ℤ` given as a row list, the kernel
certificate of `det A = d` is the list form of a fraction-free
triangularization, the same data Mathlib's `Echelon.Decomposition` carries
but checked as lists (`Hex.Matrix.DetWitness`, `checkDetList`):

- the row swaps of the pivot search, in application order; the kernel
  arranges the rows itself and reads `sign σ` off the number of swaps;
- a lower-triangular integer transform `L` given row by row with its
  `i + 1` leading entries, so its diagonal `l₀, …, lₙ₋₁` is the last entry
  of each row, all nonzero;
- the value `d`.

The check takes, for every row `i` of `L`, its products with the columns
`0, …, i` of `σA`: the first `i` vanish and the last is the diagonal entry
`uᵢ` of the upper-triangular product `U = L · σA`, so the diagonal of `U`
is computed rather than carried; then `(∏ lᵢ) · d = sign σ · ∏ uᵢ` is
checked over `Int`. Soundness in `hex-bareiss-mathlib`:
`det L · det (σA) = det U`, the determinant of a triangular matrix is the
product of its diagonal (`det_of_isLowerTriangular` and its upper form, as
`rank_eq_of_checkList` already uses), `det (σA) = sign σ · det A` by
induction over the swaps (`det_permute`, `sign_swap`), and cancellation of
the nonzero `∏ lᵢ` in `ℤ`. The producer is the row-pivoted fraction-free
elimination of `hex-bareiss` run on `[A | I]` to retain its transform, for
which `L` has diagonal `1, d₁, …, dₙ₋₁` (the leading principal minors) and
`U` has diagonal `d₁, …, dₙ`, so `d = sign σ · dₙ` and the cost of the
check is about `n³ / 3` products of minor-sized integers, the shape that
`eval_rank` pays in `Matrix.of` form and `checkRankList` avoided. A
singular matrix is certified separately and more cheaply by a nonzero
integer row vector `v` with `v · A = 0` checked as `n²` products
(`exists_vecMul_eq_zero_iff`); the elimination in echelon form yields it as
the last row of the transform. Over `ℚ` the rows are scaled to integers and
the scaling factors are checked in the kernel (`checkDetRat`,
`det_eq_of_checkRat`), as the rank SPEC plans for its rational follow-up.

Measured, this form clears the bar on every shared family by an order of
magnitude or more ([Measured record](#measured-record)); the multimodular
route of `hex-det` (triangularizations modulo several small primes plus
`Matrix.det_le` as the size bound) is not needed.

## The bar against Mathlib

A tactic ships only when, on every family of the fixture ladder below that
the pinned Mathlib tactic also accepts, its fresh-module median is below
Mathlib's, with the paired sweep of `scripts/bench/fresh_module_sweep.py`
(six samples, adjacent pairs, alternating orientation) and one kernel-only
profile per family recorded in the owning library's SPEC. "Strictly
superior" means both:

- **runtime**: a smaller median on every shared family, reported with the
  ratio and the kernel-only times, not a win on selected rungs;
  (*opt-in exception*: an arm that does not clear both halves may still
  ship as an explicitly opt-in tactic form and term form, never in a
  default simp chain, with its full family table recorded; it enters a
  default chain only on families where it wins, and the chain dispatches
  on that regime. The symbolic `det` arm of
  [hex-poly-det-mathlib](Libraries/hex-poly-det-mathlib.md) is the first
  use.)
- **scope**: every input the Mathlib tactic accepts is accepted (or, for
  symbolic entries, delegated to it inside the same tactic), and at least
  one class of input beyond it is accepted: `fun i j => …` and
  `Matrix.ofArray` literals, definitions unfolded within a budget, `ℚ`
  entries, the empty and rectangular shapes, the `%` term forms.

The comparators are the unmodified pinned `eval_det`/`norm_det`
(`Mathlib/Tactic/NormDet.lean`, Bird's algorithm with a certificate chain
normalized by `ring`) for `det` and `eval_rank`/`norm_rank` for `rank`.
Mathlib has no characteristic-polynomial tactic. For `char_poly`, compare
against Hex's existing frontend and the scalar list Berkowitz baseline on the
same `dense` 4, 8, 16, 32 signed 8-bit inputs. The packed certificate should
beat the existing frontend at each rung and clearly improve on the scalar
checker at 16 and 32. Preregister external kernel targets (1 second at 16 and
10 seconds at 32) and record any gap and the next optimization. A missed
absolute target does not withhold this competitor-free tactic. Rank has a
different arithmetic cost and is an informational comparator, not a timing
threshold for characteristic polynomials.

Fixture families (from the withdrawn SPEC, unchanged): `dense` (seeded
full-rank square integer matrices, dimensions `2, 4, 8, 16, 32`, entry
bits `8, 32`, rational variants), `structured` (tridiagonal and
Vandermonde with required pivot swaps), `singular` (duplicate rows and rank
`n − 1` products with a late failed pivot), `low-rank` (rectangular
products of known rank), `large-coefficients` (dimensions `2, 4, 8, 16`,
entry bits `64, 256, 1024`), `finite-carriers` (`Fin 7`, `Fin 8`, `ZMod`
counterparts), `closed-algebraic` (`α² = 2` blocks). The proof probes
follow `bench/HexRankMathlib/ProofProbe` (`{family}{Hex,Mathlib}.lean`
pairs against import-only baselines) under the owning library's
`proof_probes` reservation.

## Measured record

Shared host, one run each unless stated, kernel "type checking" time of the
emitted proof; the fresh-module medians are from the paired sweeps where
they exist.

| design | family | Hex | Comparator | verdict |
|---|---|---|---|---|
| `char_poly` by packed list Berkowitz | dense `16 × 16`, 8-bit | 573.5 ms | scalar lists 1.63 s | six paired samples: 2.85x kernel speedup |
| same | dense `32 × 32`, 8-bit | 5.17 s | scalar lists 29.75 s | six paired samples: 5.69x kernel speedup |
| `rank` by `checkRankList` (shipped) | dense `16 × 16` | 115 ms | `eval_rank` 864 ms | 7.5x faster; fresh-module 4.5x |
| `rank` by `checkRankList` (shipped) | `32 × 32`, rank 2 | 116 ms | `eval_rank` 7.3 s | 63x; fresh-module 21.6x |
| `rank` by `checkRank` on a `RankCert` | dense `16 × 16` | 371 s | `eval_rank` 864 ms | rejected |
| `rank` by replaying `rowReduceWith` | dense `16 × 16` | 27 s | `eval_rank` 864 ms | rejected |
| `det` by replaying `bareissReplay` (withdrawn PR) | dense `8 × 8`, 8-bit | 0.83 s (+0.82 s elaborator pre-check) | `eval_det` 0.25 s | rejected |
| same | dense `12 × 12` | 6.6 s (+6.7 s) | `eval_det` 1.5 s | rejected |
| same | dense `16 × 16` | 30.6 s (+28.9 s) | `eval_det` 5.3 s | rejected |
| `det` by Leibniz replay of `Hex.Matrix.det` | dense `6 × 6` | 6.3 s | | rejected beyond `5 × 5` |
| `det` by `checkDetList` (shipped) | dense `8 × 8`, 8-bit | 23 ms | `eval_det` 246 ms | 10.7x; fresh-module 3.3x |
| same | dense `12 × 12` | 63 ms | `eval_det` 1.48 s | 23x; fresh-module 11.7x |
| same | dense `16 × 16` | 163 ms | `eval_det` 6.9 s (one profiled run, over the size sweep's cap) | 42x; fresh-module 36x |
| same | dense `32 × 32` | 1.55 s | `eval_det` over 300 s | fresh-module 3.7 s with no `eval_det` arm |
| `det` by a left kernel vector (shipped) | singular `16 × 16` | 58 ms | `eval_det` 6.7 s (one profiled run) | 116x; fresh-module 59x |
| `det` by `checkDetRat` (shipped) | rational `8 × 8` | 39 ms | `eval_det` 351 ms (one profiled run) | 9x; fresh-module 3.5x |

Reading the literal's entries by kernel evaluation of `A i j` costs about
200 ms at `16 × 16`, more than the shipped rank check; the definitional
identification costs 6 ms. Every new tactic starts from these numbers.
