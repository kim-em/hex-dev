# hex-row-reduce-mathlib (depends on hex-row-reduce + hex-matrix-mathlib + Mathlib)

## Correspondence-only classification

The existing API is a `correspondence-only-layer`. The inverse and solve
frontends specified below add companion conformance and fresh-module proof
evidence when implemented; compiled algorithms remain in HexRowReduce.

Computational conformance owner: `HexRowReduce`
Computational performance owner: `HexRowReduce`

Mathlib correspondence for `hex-row-reduce`: connects our computable RREF / rank / span /
nullspace machinery to Mathlib's noncomputable linear-algebra definitions, via
the base `matrixEquiv` from `hex-matrix-mathlib`.

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with Mathlib's
`Matrix.rank` (noncomputable, `finrank R (LinearMap.range M.mulVecLin)`):
```lean
theorem rank_eq [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M)
```

This is deliberately a theorem about a reduced row-echelon witness, not an
arbitrary `IsEchelonForm`: the proof obtains the kernel dimension from the
computed nullspace basis, whose completeness and independence require
`IsRowReduced`. The correspondence theorem uses Mathlib's `Field`; the executable
row-reduction, span, and nullspace APIs in `HexRowReduce` use
`Lean.Grind.Field` (and `DecidableEq` where computation requires it).

**Nullspace:** Our computed nullspace basis spans exactly the kernel of the
Mathlib matrix:
```lean
theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    Submodule.span R
        (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M))
```

**Span:** The executable `IsEchelonForm.spanContains` test, called through a
reduced row-echelon witness, agrees with membership in the span of the Mathlib
matrix's rows:
```lean
theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      vectorEquiv v ∈
        Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M)))
```

This makes our row-reduction computations computable witnesses for Mathlib's
noncomputable rank/kernel/span definitions.

**Span coefficients:** The soundness theorem accepts an `IsEchelonForm`;
completeness of span testing above requires `IsRowReduced`.

```lean
theorem spanCoeffs_eq_linearCombination [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsEchelonForm M D) (v : Vector R m) (c : Vector R n) :
    E.spanCoeffs v = some c →
      vectorEquiv v =
        Fintype.linearCombination R (_root_.Matrix.row (matrixEquiv M)) (vectorEquiv c)
```

All four theorems above exist in
`HexRowReduceMathlib/RankSpanNullspace.lean`, in namespace
`HexMatrixMathlib`. In particular, `rank_eq` and `nullspace_span_eq_ker`
require Mathlib `[Field R]` but no `DecidableEq R` when supplied a reduced
witness; instantiating that witness with executable `rowReduce` additionally
requires `[DecidableEq R]`.

## Field inverse correspondence

The inverse and solve theorems in this section and the next are required
extensions, paired with the computational contracts in
[hex-row-reduce](../../HexRowReduce/SPEC/hex-row-reduce.md#field-inverse-and-complete-linear-solve).
They live in namespace `HexMatrixMathlib`. Their coefficient assumptions
are Mathlib `[Field F] [DecidableEq F]`, using the induced
`Field.toGrindField` instance for the executable calls. Choose that instance
before defining inputs and outputs, for example with
`attribute [local instance 2000] Field.toGrindField` in examples. Do not assume
it equals a separately installed `Lean.Grind.Field F` instance, or that
results computed at another instance are directly accepted by these theorems.
Use `matrixEquiv` for matrices and `vectorEquiv` for vectors throughout.

```lean
theorem inverse?_eq_inv [Field F] [DecidableEq F]
    (A B : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = some B → matrixEquiv B = (matrixEquiv A)⁻¹

theorem inverse?_eq_none [Field F] [DecidableEq F]
    (A : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = none ↔ (matrixEquiv A).det = 0
```

Together these require the full specification: under nonzero determinant,
`Option.map matrixEquiv (Hex.Matrix.inverse? A) = some ((matrixEquiv A)⁻¹)`;
under zero determinant the result is `none`. Transport the two product
identities of computational `inverse?_spec` and use uniqueness of inverse.

The pinned Mathlib names the noncomputable `Inv` instance `Matrix.inv`;
`A⁻¹` is its nonsingular inverse, defined using `Ring.inverse A.det` and
the adjugate in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`.
There is no separate `Matrix.nonsing_inv` definition in that file. The
existing `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` require
`IsUnit A.det`, over `[CommRing F]` and finite decidable square indices;
a nonzero determinant over a field supplies this hypothesis. At singular
input Mathlib's inverse is zero, whereas the executable returns `none`;
no theorem should identify that `none` with an inverse witness.

For determinant completeness, apply existing `rank_eq` to
`Hex.Matrix.rowReduce_isRowReduced A`, identifying `rowReduce_rank A`
with the Mathlib rank. Existing `Matrix.rank_of_det_ne_zero` in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` gives full rank over
`[CommRing F] [IsDomain F]` with finite decidable square indices. The
computational `inverse?_isSome` then gives success. Conversely, success
and the transported product identity imply nonzero determinant by existing
`Matrix.det_ne_zero_of_right_inverse` (commutative ring, nontrivial
coefficients, finite decidable square indices). Thus `none` is equivalent
to determinant zero without adding a determinant computation or dependency
to `HexRowReduce`.

## Linear solve correspondence and completeness

```lean
theorem solve?_spec [Field F] [DecidableEq F]
    (A : Hex.Matrix F n m) (b : Vector F n) (s : Hex.Matrix.SolveData A) :
    Hex.Matrix.solve? A b = some s →
      (matrixEquiv A).mulVec (vectorEquiv s.1) = vectorEquiv b ∧
      s.2 = Hex.Matrix.nullspaceBasisMatrix A ∧
      ∀ x : Fin m → F,
        (matrixEquiv A).mulVec x = vectorEquiv b ↔
          x - vectorEquiv s.1 ∈
            LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv A))

theorem solve?_eq_none [Field F] [DecidableEq F]
    (A : Hex.Matrix F n m) (b : Vector F n) :
    Hex.Matrix.solve? A b = none ↔
      ¬ ∃ x : Fin m → F, (matrixEquiv A).mulVec x = vectorEquiv b
```

Also require the explicit parameter form of the solution-set theorem:
for every successful result `s` and `x : Fin m → F`,

```lean
(matrixEquiv A).mulVec x = vectorEquiv b ↔
  ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → F,
    x = vectorEquiv s.1 + (matrixEquiv s.2).mulVec c
```

The coefficients are unique because the returned columns are the computed
basis with identity on the free coordinates. Use existing
`nullspace_span_eq_ker (Hex.Matrix.rowReduce_isRowReduced A)` to identify
the span of these columns with the kernel; the existing private
`nullspace_linearIndependent` in `RankSpanNullspace.lean` takes `[Field F]`
and an `IsRowReduced` witness. Reuse it within that module, or expose it
if the new correspondence theorems live in a separate module. This gives
an affine translate of the entire kernel, rather than only a residual
check on one solution. The
existing `vectorEquiv_mulVec` in `HexMatrixMathlib/Vector.lean` transports
matrix-vector products over `[Semiring F]`.

For every `Hex.Matrix.solve A b = .error y`, require
`_root_.Matrix.vecMul (vectorEquiv y) (matrixEquiv A) = 0` and
`dotProduct (vectorEquiv y) (vectorEquiv b) ≠ 0`. Moreover failure is
equivalent to existence of such a left-kernel separator. Prove the
constructive direction using the actual returned row of the RREF
transform, and the converse by applying an arbitrary separating row
functional to a hypothetical solution. No resource bound or additional
consistency hypothesis may appear in these completeness statements.

## Verification and ownership

Check the computational SPEC's boundary cases through these
correspondence theorems:

- For `0 × 0`, Mathlib's determinant is `1`, the inverse is the empty
  identity, and solve returns the unique empty solution with no basis
  columns. No theorem assumes a positive dimension.
- For `0 × m`, the kernel is the full space and the returned basis is the
  standard basis. For `n × 0`, consistency is exactly `b = 0`.
- For singular `[[1, 0], [0, 0]]`, determinant zero forces inverse
  failure, while RHS `[a, 0]` has the affine solution set `[a, t]`.
- For `[[1, 0, 0], [1, 0, 0]]` with RHS `[0, 1]`, the returned separator
  `[-1, 1]` has zero left product and dot product `1`, proving the
  rectangular system inconsistent over any field.

Exercise the carrier interpretations in a monorepo build-only module
`Examples/RowReduce.lean`, registered in `HexReleaseExamples`, outside the
generic companion's imports. These examples contain proof checks, not
fixture emission or oracle tests.

- `Rat`: computational conformance uses Lean's rational field instance.
  Companion examples separately select the Mathlib-induced instance before
  defining the matrices and calling inverse/solve. Equality of the two bundled
  instances is not assumed. Transporting an already computed result between
  them would require an additional explicit agreement proof.
- `RationalFn Rat`: follow
  [hex-rational-fn-mathlib's instance contract](../../HexRationalFnMathlib/SPEC/hex-rational-fn-mathlib.md#coefficient-instances-and-representation).
  Choose the Mathlib-induced lightweight field on `Rat` before forming the
  rational-function type, and the induced field on that type before forming
  row-reduction calls. Use `HexRationalFnMathlib.field` and its equivalence
  with `RatFunc Rat` for these examples. Computational fixtures separately
  exercise the implementation with its executable instances. Changing
  instance priorities does not convert previously defined values.
- `ZMod64 p`: the tree provides an executable field under `Bounds p` and
  `PrimeModulus p`, but no Mathlib `Field (ZMod64 p)`. For these examples,
  transport the computational success and failure equations entrywise through
  the existing `HexModArithMathlib.ZMod64.equiv` to `ZMod p`. Supply the prime
  hypotheses for the executable and Mathlib fields. Multiplication, addition,
  zero preservation and injectivity transport the inverse identities and
  separating witness. Surjectivity also transports the quantified solution
  and coefficient vectors, giving completeness and the affine solution set
  over `ZMod p`. These example-level transport proofs are new obligations.
  They use the ring equivalence without assuming a missing `toZMod_inv` lemma
  or a Mathlib field structure on `ZMod64 p`, and do not require transporting
  the elimination algorithm itself.

`HexRowReduce` owns the exact FLINT/SymPy conformance and dimension/height
benchmarks specified in its SPEC. This companion owns proof checks of the
transported success, failure, and solution-set statements; it adds no
benchmark executable. The domain certificate inverse described in hex-rank
and the direct field inverse agree after transport to a common field and
undoing the certificate's row/column selections, by uniqueness of inverse;
that consumer-level comparison adds no dependency between the libraries.

## Frontend implementation and validation

The tactic contracts below are design requirements. Their kernel-certificate
subsections specify additions owned by the Mathlib-free algorithm library;
they do not move that code into this companion. When implementing those
additions, cross-link the algorithm's kernel-certificate SPEC to this contract.
Keep existing phase evidence as evidence for the existing correspondence only.
Before activating the frontend, remove `correspondence_only: true` if present,
add `proof_probes: [bench/HexRowReduceMathlib/ProofProbe]`, and reopen the
library's conformance/performance obligations: cap `done_through` at `2` until
the new build-only proof tests pass, then at `3` until complete proof evidence
passes. Do not add an empty reservation while retaining a completed Phase 4.
This SPEC-only change does not alter the manifest or attest implementation.

Proof tests live in `HexRowReduceMathlib/Tests.lean`, built with the ordinary
library; malformed list certificates also belong in the algorithm library's
Mathlib-free conformance driver. Proof probes are fresh modules, not runtime
oracle drivers or Mathlib-importing benchmark executables. Each frontend uses
`HexRowReduceMathlib/Tactic.lean`; result records and list soundness belong
in `HexRowReduceMathlib/Kernel.lean`. No library name changes.

For the named families below, shipping requires complete clean-tree evidence
under the `absolute_only` mode of
[SPEC/benchmarking.md](../../SPEC/benchmarking.md#fresh-module-proof-evidence).
Preregister six rounds and a per-candidate absolute build budget of 60 seconds
on the measurement host for every stated rung. Every candidate sample must
meet it; report the median and kernel-only time as well. A timeout, incomplete
pair, budget failure or provenance mismatch blocks the frontend's performance
sign-off. This is an operational shipping gate, not an asymptotic or portable
wall-time claim. Retain slow completed samples; do not trim the ladder to get
a passing verdict. Any budget revision requires an explicit SPEC amendment.

## The `inverse` tactic

This is a required frontend extension to the field inverse correspondence
above, conditional on implementing its algorithm contracts from
[issue #10181](https://github.com/kim-em/hex-dev/issues/10181). Follow
[the matrix tactic protocol](../../SPEC/matrix-tactics.md) and
[the `rank` template](../../HexRankMathlib/SPEC/hex-rank-mathlib.md#the-rank-tactic).
List witness/checker/producer additions belong to HexRowReduce and their
Mathlib transport and frontend belong here, without a new library.

### Goals, result and carriers

Declare non-reserved `inverse` and term form `inverse% A`. For closed square
`A B : Matrix (Fin n) (Fin n) F`, close `A * B = 1` and `A⁻¹ = B`,
including reversed equality orientations. The new `InverseResult A` is a
tagged dependent result with two alternatives:

- `invertible`: literal `value : Matrix (Fin n) (Fin n) F`,
  `A * value = 1`, `value * A = 1`, and `A⁻¹ = value`;
- `singular`: literal `kernel : Fin n → F`, `kernel ≠ 0`,
  `A.mulVec kernel = 0`, `A.det = 0`, and `A⁻¹ = 0`.

The singular alternative is mathematical success in term mode, not a
producer error. It closes `A⁻¹ = 0` but cannot close `A * B = 1`. For
`n = 0`, return the empty identity in the invertible alternative; no
nonzero kernel vector exists. On invertible inputs check the stated `B`
against the unique computed inverse.

Soundness assumes Mathlib `[Field F] [DecidableEq F]` and coherent induced
`Field.toGrindField`, as in the inverse correspondence above. The initial
frontend supports closed `ℚ` entries including fractions; an arbitrary
field instance does not imply a codec. Prime `ZMod p` is an extension once
its codec and field transport are proved; composite moduli and symbolic
entries are outside this handler. Rational functions are covered by the
algorithm SPEC, but are not promised by this numeric frontend.

Use [the shared literal layer](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#matrix-literals)
for both `A` and `B`. Request against its SPEC field-aware term elaboration,
rational/residue codecs with proved arithmetic agreement, and vector
literal identification for the kernel witness. These requests are shared
with `min_poly` and `solve`, not separate local reifiers.

### Kernel certificate and soundness

The planned `inverse?` returns a matrix, not an independent certificate or
a singularity witness. Its `inverse?_spec` requires the producer equation
`inverse? A = some B`; the tactic must not discharge that by replaying RREF.
Require a new list `InverseWitness` and `checkInverseList`. In the invertible
case the quoted inverse is the witness: check its exact square shape and
`A * B = I` and `B * A = I`. In the singular case check a vector of length
`n`, a nonzero coordinate (with its index in range), and `A * v = 0`.
The list products use only exposed structural recursion on `Nat`/`Int` data.
For `ℚ`, follow the scaled-integer boundary of `checkDetRat` in
`HexBareiss/Kernel.lean`. Keep each literal's row list at `Rat` for its
`rfl` identification and check agreement with integer rows and a positive
common denominator using entrywise numerator/denominator cross products.
Encode each witness matrix/vector with its own common denominator. For
`A = Z / d` and `B = V / e`, check `Z * V = (d * e) I`; for
`v = w / s`, check `Z * w = 0`. Thus products and sums are integer list
arithmetic, not repeated addition of unreduced fractions. Reject zero scales;
the codec supplies the proved literal/encoding agreement. Product bit heights
are bounded by the summed operand heights plus `O(log(n + 1))`; scale and
witness numerator heights are recorded separately from original input heights.
No `Array`, `Vector`, `Fin`, `Finset`, `Hex.Matrix`, well-founded recursion,
field inversion or producer execution occurs on the reduction path.

Require new `inverse_of_checkList` to transport the successful product checks
and `hA : A = ofLists ...` (and the analogous identification of `B`) to both
Mathlib product identities and `A⁻¹ = B`. It uses inverse uniqueness and
the same Mathlib inverse theory as the correspondence above, independently
of `inverse?_spec`. Require a separate singular soundness lemma: a nonzero
right-kernel vector implies determinant zero over a field and hence zero
Mathlib inverse. These are new arbitrary-witness transport lemmas. They
must not assume a positive dimension, nonzero determinant in the singular
case, or that quoted data is definitionally the producer's output.

Required result signature in `HexRowReduceMathlib/Kernel.lean` (namespace
`HexMatrixMathlib`), using the same coherent field instance as above:

```lean
inductive InverseResult {F : Type u} [Field F] {n : Nat}
    (A : Matrix (Fin n) (Fin n) F) where
  | invertible (value : Matrix (Fin n) (Fin n) F)
      (right_inv : A * value = 1) (left_inv : value * A = 1)
      (inv_eq : A⁻¹ = value)
  | singular (kernel : Fin n → F) (nonzero : kernel ≠ 0)
      (annihilates : A.mulVec kernel = 0) (det_eq : A.det = 0)
      (inv_eq : A⁻¹ = 0)

-- Initial rational checker in HexRowReduce/Kernel.lean, namespace Hex.Matrix:
def checkInverseList (n : Nat) (rows : List (List Rat))
    (c : InverseWitness) : Bool

-- Companion constructor; its proof fields come from the product/kernel lemmas.
noncomputable def inverse_of_checkList {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (List Rat))
    (c : Hex.Matrix.InverseWitness)
    (hA : A = HexMatrixMathlib.ofLists n n rows)
    (hc : Hex.Matrix.checkInverseList n rows c = true) : InverseResult A
```

`InverseWitness` is a tagged list record: an invertible branch stores the
scaled input and inverse blocks; a singular branch stores the scaled input
block, scaled kernel vector and nonzero-coordinate index. Every scale is a
`Nat` and every numerator is an `Int`. The constructor's projection theorems
identify its returned value/vector with that branch's decoded literals.

### Producer and proof assembly

Run the compiled field RREF inverse path once, retaining its reduced data.
On failure of the full-rank test, extract a nonzero column of its existing
nullspace basis; do not claim `inverse?` itself returns this vector. This
witness-producing wrapper is a new HexRowReduce obligation for this tactic,
requested against its SPEC's §Field inverse and complete linear solve. That
section excludes such a wrapper only from the earlier algorithm extension;
it must be extended before this frontend ships. The `inverse?` API stays intact.
Re-check either list witness before quoting.

Follow `HexRankMathlib/Kernel.lean` and `Tactic.lean`: shared literal
identification, list soundness wrapper, and one synchronous auxiliary theorem
covering all proof fields or the requested orientation. Do not kernel
pre-check. Other operations/carriers are `notApplicable`; an in-fragment
missing capability or exceeded budget is `declined`; a false target reports
the inverse or certified singularity; malformed output or kernel rejection
is `failure`. No singular branch fabricates an inverse product witness.

### Conformance and proof probes

Test both equalities and orientations, both term-result alternatives, all
literal routes, fractions, required pivot swaps, singular nonzero matrices,
the zero matrix, and `0 × 0`. Refute wrong inverse entries, wrong shapes,
zero denominators, zero kernel vectors, out-of-range nonzero-coordinate
indices and nonzero residuals. Test that singular `A⁻¹ = 0` succeeds while
`A * 0 = 1` is rejected for positive dimensions. Audit axioms: only
`propext`, `Classical.choice`, `Quot.sound`.

On implementation reserve `bench/HexRowReduceMathlib/ProofProbe` for both
frontends, with inverse modules below `Inverse/`. Named seeded families:
`dense-invertible`, `pivot-swaps`, `singular-kernel` (rank `n - 1` and
`n / 2`), and `rational-height`; dimensions `2, 4, 8, 16`, input heights
`8, 32` bits, and `64, 256` for the height family. Profile product and inverse
goals separately, including singular inverse goals. Mathlib has no dedicated
inverse tactic. Include an informational matched proof using entrywise
`simp [Matrix.mul_apply]`/`norm_num` for small closed product goals; report
whether it closes each rung rather than presuming a complete competitor.
Record six complete fresh-module samples paired with
import-only baselines, adjacent and alternating orientation, absolute
wall times/medians, baseline deltas and one kernel-only profile per family
per [SPEC/benchmarking.md](../../SPEC/benchmarking.md#fresh-module-proof-evidence).
Include certificate entry counts/serialized bytes, largest numerator and
denominator heights, emitted artifact sizes, axiom sets and full
source/toolchain/host provenance. Retain completed samples and timeouts;
preregister operational caps. Compiled benchmarks stay in HexRowReduce.

## The `solve` tactic

This is a required extension conditional on the complete solve algorithm and
correspondence above, not an assertion that `solve?` and its theorems already
exist. Follow [the matrix tactic protocol](../../SPEC/matrix-tactics.md) and
[the `rank` template](../../HexRankMathlib/SPEC/hex-rank-mathlib.md#the-rank-tactic).
It shares HexRowReduce's field certificate primitives with `inverse`.

### Goals, result and carriers

Declare non-reserved `solve` and term form `solve% A b`. Add parser
regression tests for the bare matrix tactic, term form and ordinary
identifiers/function applications named `solve`. For closed
`A : Matrix (Fin n) (Fin m) F`, `b : Fin n → F`, `x : Fin m → F`, accept
`A.mulVec x = b` and its reverse. The stated `x` need not be the producer's
canonical particular solution: check its residual directly. Also accept
`∃ x, A.mulVec x = b` and `¬ ∃ x, A.mulVec x = b` using the corresponding
certified outcome.

The new dependent `SolveResult A b` has two alternatives:

- `consistent`: a literal particular solution `value : Fin m → F`, a
  literal `nullity : Nat`, a literal matrix
  `basis : Matrix (Fin m) (Fin nullity) F`, `A.mulVec value = b`, and
  `∀ x, A.mulVec x = b ↔ ∃! c, x = value + basis.mulVec c`;
- `inconsistent`: a literal `separator : Fin n → F`,
  `Matrix.vecMul separator A = 0`, `dotProduct separator b ≠ 0`,
  and `¬ ∃ x, A.mulVec x = b`.

The particular solution has zero free coordinates and the basis uses the
algorithm SPEC's increasing free-column order. The term result certifies the
entire affine space, not just one residual or linearly independent kernel
vectors. Its dimensions are quoted naturals, not a reduction of
`rowReduce_rank A`. A certified inconsistent system is a successful negative
term result; on a positive goal it reports the checked separator and nonzero
dot product, then leaves the goal unproved.

Use the same Mathlib field assumptions, initial `ℚ` fragment, optional prime
`ZMod p` arm and instance discipline as `inverse`. Import matrix recognition
from [the shared literal layer](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#matrix-literals).
Request against that SPEC the field codecs and closed vector adapters for
`b` and `x`, with their proved identifications; share the requests with
`inverse`. Unsupported symbolic fields/rational-function expressions do not
inherit a frontend merely from their executable field instance.

### Kernel certificate and soundness

The planned `solve` returns either `SolveData A` or a separating row;
`solve?` forgets the separator. The planned success/failure theorems have
producer-equation hypotheses, so their invocation is not a kernel checker.
Require list `SolveWitness`/`checkSolveList` in HexRowReduce with separate
checks for a particular residual, complete affine data, and inconsistency.

- For a supplied solution goal, check exact shapes and `A * x = b` directly.
- For term mode or an existential success, retain RREF data `R`, transforms
  `U`, `W`, rank `r` and pivot/free-column lists from the compiled solve.
  Check `U * A = R`, `U * W = I`, both rank bounds, the full RREF clauses
  (sorted in-range pivots, pivot ones, zeros before and above/below pivots,
  zero trailing rows), and that pivots/free columns partition all `m`
  columns in increasing order. Check `nullity = m - r`, `A * value = b`,
  zero free coordinates of `value`, and that every basis column has the
  prescribed identity free coordinates and negative RREF pivot entries.
  These last checks certify completeness and unique coefficients; checking
  only `A * basis = 0` would not.
- For inconsistency, check separator length `n`, `y * A = 0` and
  `y · b ≠ 0`. This does not require an RREF certificate.

All matrices/vectors are exact-length lists, indices are checked naturals,
and field scalars use the positive-common-denominator integer blocks
of `inverse`, clearing denominators once per identity. All reduction-path
definitions are exposed structural list
recursions, with no `Array`, `Vector`, `Fin`, `Finset`, `Hex.Matrix`,
well-founded recursion or replay of row reduction/solve/nullspace search.

Required new `solve_of_checkList` proves the residual equality for decoded
lists; the complete branch additionally reconstructs an `IsRowReduced`
witness from the checked identities and shape. The existing
`HexMatrixMathlib.nullspace_span_eq_ker` takes Mathlib `[Field F]` and
`IsRowReduced M D`, and identifies the computed nullspace span with the
kernel. Reuse it, plus the free-coordinate identity for uniqueness, to
prove the term record's affine-space statement. Expose or reuse the private
independence proof as specified in the correspondence above. A separate
separator lemma transports the zero left product and nonzero dot product
and rules out every solution by associativity. None of these new lemmas
requires `solve A b = ...`. Wrappers take matrix/vector literal
identifications for the actual Mathlib goal, just like rank's `hA` wrapper.

Required result signature in `HexRowReduceMathlib/Kernel.lean`, namespace
`HexMatrixMathlib`; `c` is explicitly indexed by the quoted nullity:

```lean
inductive SolveResult {F : Type u} [Field F] {n m : Nat}
    (A : Matrix (Fin n) (Fin m) F) (b : Fin n → F) where
  | consistent (value : Fin m → F) (nullity : Nat)
      (basis : Matrix (Fin m) (Fin nullity) F)
      (solution : A.mulVec value = b)
      (complete : ∀ x : Fin m → F, A.mulVec x = b ↔
        ∃! c : Fin nullity → F, x = value + basis.mulVec c)
  | inconsistent (separator : Fin n → F)
      (annihilates : Matrix.vecMul separator A = 0)
      (separates : dotProduct separator b ≠ 0)
      (impossible : ¬ ∃ x : Fin m → F, A.mulVec x = b)

-- Initial rational residual checker, namespace Hex.Matrix:
def checkSolutionList (n m : Nat) (rows : List (List Rat))
    (rhs candidate : List Rat) : Bool

-- Direct residual soundness, namespace HexMatrixMathlib:
theorem solve_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℚ) (b : Fin n → ℚ) (x : Fin m → ℚ)
    (rows : List (List Rat)) (rhs candidate : List Rat)
    (hA : A = ofLists n m rows) (hb : b = vecOfList n rhs)
    (hx : x = vecOfList m candidate)
    (hc : Hex.Matrix.checkSolutionList n m rows rhs candidate = true) :
    A.mulVec x = b
```

The direct residual checker obtains common denominators by a structural
list fold before integer products. The complete `checkSolveList` additionally
takes a tagged `SolveWitness`: the consistent branch contains the scaled
RREF/transform/inverse, pivot and free-column lists, rank, particular solution
and basis; the inconsistent branch contains the scaled separator. Its new
companion constructor `solveResult_of_checkList` takes the analogous `hA`,
`hb` and accepted check and returns `SolveResult A b`, with projection
lemmas fixing its literal data to the witness. These types avoid the existing
`SolveData A`'s producer-dependent dimension on the reduction path.

### Producer and proof assembly

For complete/negative output call compiled `solve` once, retaining RREF data
and its inverse transform for the complete witness. Retaining the inverse
transform in this wrapper is a new certificate-producer obligation; no
elimination is rerun merely to recover a dependent output size. For a stated
solution, the direct residual check accepts any valid `x`; if it fails, use
the complete producer to distinguish a wrong candidate from inconsistency.
Re-check all emitted list data in compiled code before quoting.

Follow `HexRankMathlib/Kernel.lean` and `Tactic.lean`: identify literals once,
quote the witness, and build all proof fields/the goal through one synchronous
auxiliary theorem. No preliminary kernel check or native proof trust. Other
operations/carriers are `notApplicable`; missing in-fragment codecs or
budgets are `declined`. A wrong candidate reports its residual and, when
consistent, a certified particular solution; inconsistency reports the
checked separator. Only a producer bug, malformed certificate or kernel
rejection is `failure`, never an ordinary inconsistent system.

### Conformance and proof probes

Test rectangular systems, a noncanonical valid stated solution, both
existential outcomes, both equation orientations, both term records and
unique coefficient reconstruction. Include `0 × 0`, `0 × m` (full kernel),
`n × 0` (consistent exactly for zero RHS), rank zero, non-leading pivots,
fractions and all literal routes. Refute corrupted residuals, missing or
duplicate basis columns, a zero or incomplete kernel basis, bad free-column
partitions, invalid RREF shapes/transforms, wrong nullity, zero denominators,
and separators with either nonzero left product or zero dot product.
Audit the accepted theorem axioms against `propext`, `Classical.choice`,
`Quot.sound` only, including negative results.

Use modules below `bench/HexRowReduceMathlib/ProofProbe/Solve` in the shared
reservation. Named seeded families: `square-unique`, `tall-consistent`
(`2n × n`), `wide-affine` (`n × 2n`), `deficient-affine` (rank `n / 2`),
and `inconsistent-separator` (the same deficient matrices with inconsistent
RHS), at `n = 2, 4, 8, 16` and rational input heights `8, 32, 128` bits.
Measure the supplied-solution and complete-record surfaces separately.
There is no dedicated Mathlib solve tactic. For supplied-solution goals,
include an informational matched entrywise `simp [Matrix.mulVec]`/`norm_num`
proof on small rungs where it closes the same goal. This normalization
baseline does not compute a solution or certify the complete affine space;
record absolute numbers for all surfaces.
Per [SPEC/benchmarking.md](../../SPEC/benchmarking.md#fresh-module-proof-evidence),
use six adjacent import-baseline/probe pairs, alternating orientation, retain
all raw build times/medians and deltas, and record one kernel-only profile
per family. Record certificate entry counts/serialized bytes, scalar heights,
emitted artifact sizes, axiom sets and exact source/toolchain/host provenance.
Retain every completed sample and timeout, with preregistered operational
caps. Compiled solver/certificate benchmarks remain in HexRowReduce.
