# Matrix tactics

Proof-producing tactics on closed matrices (`rank`, `det`, `char_poly`, and
later `min_poly`, `inverse`, `solve`) are not a library of their own. Each
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
| `det` | `A.det = d` | `hex-bareiss`: a kernel-form triangular certificate produced by fraction-free elimination | `hex-bareiss-mathlib` | to do: https://github.com/kim-em/hex-dev/issues/10211; see [The determinant certificate](#the-determinant-certificate) |
| `char_poly` | `A.charpoly = p` | `hex-char-poly`: the Berkowitz certificate, in kernel form | `hex-char-poly-mathlib` | frontend exists in `HexCharPoly`/`HexCharPolyMathlib`; kernel form and measurement to do: https://github.com/kim-em/hex-dev/issues/10212 |
| `rank`, symbolic entries | `A.rank = r` (conditional), `A.rank ≤ r`, generic rank of the reified matrix | `hex-generic-rank`: hex-rank's certificate at `MvPoly` | `hex-generic-rank-mathlib`: a second handler on the `rank` syntax kind; `checkRank_sound_at` | specified: [hex-generic-rank-mathlib](Libraries/hex-generic-rank-mathlib.md) |
| literal layer | reading `!![…]`, `Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray xs h` | none | `hex-matrix-mathlib`: `ofLists`, `vecOfList`, literal recognition, definitional identification | currently inside `hex-rank-mathlib`; to move down: https://github.com/kim-em/hex-dev/issues/10213 |

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
  handler declines them. For `rank` that handler is specified in
  [hex-generic-rank-mathlib](Libraries/hex-generic-rank-mathlib.md), with
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

The proof is assembled as one auxiliary theorem (`mkAuxTheorem` with
asynchronous checking off), so the kernel checks the certificate exactly
once and the tactic sees a rejection and can diagnose it (false target,
producer bug, or an entry the kernel cannot reduce). The elaborator does
not pre-evaluate the check with `Kernel.whnf` and then let the kernel check
it again; that doubled the cost of the withdrawn `det`.

## Kernel discipline

Design principle 11, as `hex-rank` made it concrete: everything on the
kernel's path is a list of `Nat` or `Int`, read by structural recursion,
with arithmetic through `Nat.mul`, `Nat.add`, `Nat.mod`, `Int.mul`,
`Int.add` and comparisons through `Nat.beq`, `Nat.blt` and `Int.decEq`.
No `Array`, `Vector`, `Fin`, `Finset`, `Hex.Matrix`, `Matrix.of`, `dite`
or well-founded recursion appears on the path, every definition on it is
`@[expose]`, and a Mathlib literal is identified with its row list
definitionally (`vecOfList (k + 1) (a :: l)` unfolds to
`vecCons a (vecOfList k l)`, so `!![…] = ofLists n m L` is `rfl`), never
by evaluating `A i j` through `Matrix.of` inside the arithmetic.

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
but checked as lists:

- a row arrangement `σ` (the swaps of the pivot search, as a list of pairs,
  or the row order as a list), with `sign σ` computed by the kernel from the
  list;
- a lower-triangular integer transform `L` given row by row with its
  leading entries only, and its diagonal `l₀, …, lₙ₋₁`, all nonzero;
- the diagonal `u₀, …, uₙ₋₁` of the upper-triangular product, with the
  check that every entry of `L · (σ A)` below the diagonal is `0` and the
  diagonal is `u`;
- the value `d` with `(∏ lᵢ) · d = sign σ · ∏ uᵢ` checked over `Int`.

Soundness in `hex-bareiss-mathlib`: `det L · det (σ A) = det U`, the
determinant of a triangular matrix is the product of its diagonal
(`det_of_isLowerTriangular` and its upper form, as `rank_eq_of_checkList`
already uses), `det (σ A) = sign σ · det A`, and cancellation of the
nonzero `∏ lᵢ` in `ℤ`. The producer is the row-pivoted fraction-free
elimination of `hex-bareiss` extended to retain its transform, for which
`L` has diagonal `1, d₁, …, dₙ₋₁` (the leading principal minors) and
`U` has diagonal `d₁, …, dₙ`, so `d = dₙ` and the cost of the check is
about `n³ / 6` products of minor-sized integers, the shape that `eval_rank`
pays in `Matrix.of` form and `checkRankList` avoided. A singular matrix is
certified separately and more cheaply by a nonzero integer vector `v` with
`A ·ᵥ v = 0` checked as `n²` products (`exists_mulVec_eq_zero_iff`, or
directly `det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors`). Over `ℚ`
the rows are scaled to integers and the scaling factor is checked in the
kernel, as the rank SPEC plans for its rational follow-up.

This is a design to be measured, not a promise: the requirement is the bar
below, and if the triangular form does not clear it, the multimodular
route of `hex-det` (triangularizations modulo several small primes plus
`Matrix.det_le` as the size bound) is the next candidate.

## The bar against Mathlib

A tactic ships only when, on every family of the fixture ladder below that
the pinned Mathlib tactic also accepts, its fresh-module median is below
Mathlib's, with the paired sweep of `scripts/bench/fresh_module_sweep.py`
(six samples, adjacent pairs, alternating orientation) and one kernel-only
profile per family recorded in the owning library's SPEC. "Strictly
superior" means both:

- **runtime**: a smaller median on every shared family, reported with the
  ratio and the kernel-only times, not a win on selected rungs;
- **scope**: every input the Mathlib tactic accepts is accepted (or, for
  symbolic entries, delegated to it inside the same tactic), and at least
  one class of input beyond it is accepted: `fun i j => …` and
  `Matrix.ofArray` literals, definitions unfolded within a budget, `ℚ`
  entries, the empty and rectangular shapes, the `%` term forms.

The comparators are the unmodified pinned `eval_det`/`norm_det`
(`Mathlib/Tactic/NormDet.lean`, Bird's algorithm with a certificate chain
normalized by `ring`) for `det` and `eval_rank`/`norm_rank` for `rank`.
Mathlib has no characteristic-polynomial tactic; `char_poly`'s bar is an
absolute one, a kernel time on the `dense` ladder no worse than the shipped
`rank` at the same size, and a paired comparison against `decide`-free
elaboration of the same goal by `simp [Matrix.charpoly, …]` on the
dimensions where that terminates.

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

| design | family | Hex | Mathlib | verdict |
|---|---|---|---|---|
| `rank` by `checkRankList` (shipped) | dense `16 × 16` | 115 ms | `eval_rank` 864 ms | 7.5x faster; fresh-module 4.5x |
| `rank` by `checkRankList` (shipped) | `32 × 32`, rank 2 | 116 ms | `eval_rank` 7.3 s | 63x; fresh-module 21.6x |
| `rank` by `checkRank` on a `RankCert` | dense `16 × 16` | 371 s | `eval_rank` 864 ms | rejected |
| `rank` by replaying `rowReduceWith` | dense `16 × 16` | 27 s | `eval_rank` 864 ms | rejected |
| `det` by replaying `bareissReplay` (withdrawn PR) | dense `8 × 8`, 8-bit | 0.83 s (+0.82 s elaborator pre-check) | `eval_det` 0.25 s | rejected |
| same | dense `12 × 12` | 6.6 s (+6.7 s) | `eval_det` 1.5 s | rejected |
| same | dense `16 × 16` | 30.6 s (+28.9 s) | `eval_det` 5.3 s | rejected |
| `det` by Leibniz replay of `Hex.Matrix.det` | dense `6 × 6` | 6.3 s | | rejected beyond `5 × 5` |

Reading the literal's entries by kernel evaluation of `A i j` costs about
200 ms at `16 × 16`, more than the shipped rank check; the definitional
identification costs 6 ms. Every new tactic starts from these numbers.
