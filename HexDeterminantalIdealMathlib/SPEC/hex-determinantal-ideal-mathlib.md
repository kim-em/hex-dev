# hex-determinantal-ideal-mathlib

Correspondence between the executable minors of
[hex-determinantal-ideal](../../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md) and Mathlib's
`Matrix.det` of a `submatrix`, and the rank-versus-minors theorem stated for
`Matrix.rank` under an arbitrary ring homomorphism into a field.
Dependencies are `HexDeterminantalIdeal`, `HexDeterminantMathlib`,
`HexRowReduceMathlib` and `HexMvPolyMathlib`, plus Mathlib. The
computational contracts, the conventions at `r = 0` and `r > min n m`, and
the Mathlib-free proof route are in the computational SPEC and are not
restated here.

This library is `correspondence_only: true`, with comparator absence class
**correspondence-only-layer**. It owns no runtime search, conformance
driver or benchmark process. Build-only examples live in
`HexDeterminantalIdealMathlib/Tests.lean`.

Computational conformance owner: `HexDeterminantalIdeal`.

Computational performance owner: `HexDeterminantalIdeal`.

## Transport

Over `[CommRing R]`, with `matrixEquiv` from `HexMatrixMathlib` and
`det_eq` from `HexDeterminantMathlib`:

```lean
theorem matrixEquiv_map (A : Hex.Matrix R n m) (f : R → S) :
    matrixEquiv (A.map f) = (matrixEquiv A).map f
theorem matrixEquiv_selectedSubmatrix (A : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k) :
    matrixEquiv (Hex.Matrix.selectedSubmatrix A rows cols) =
      (matrixEquiv A).submatrix rows.get cols.get
theorem det_selectedSubmatrix_eq (A : Hex.Matrix R n m) (rows cols) :
    Hex.Matrix.det (Hex.Matrix.selectedSubmatrix A rows cols) =
      ((matrixEquiv A).submatrix rows.get cols.get).det
theorem map_minors [CommRing S] (φ : R →+* S) (A : Hex.Matrix R n m) (r : Nat) :
    (Hex.Matrix.minors r A).map φ = Hex.Matrix.minors r (A.map φ)
```

`map_minors` is `RingHom.map_det` read through `det_selectedSubmatrix_eq`
and `matrixEquiv_map`, applied to each member of the enumeration. It is the
only place a homomorphism property of `φ` is used, so the headline theorem
below holds for every `RingHom`, including evaluation of polynomials,
reduction modulo a prime and the inclusion of a domain into its fraction
field.

## The headline theorem

Over `[CommRing R]`, `[Field K]`, `φ : R →+* K`:

```lean
theorem rank_lt_iff_minors_map_eq_zero (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, φ M = 0
theorem le_rank_iff_exists_minor_map_ne_zero (A : Hex.Matrix R n m) (r : Nat) :
    r ≤ ((matrixEquiv A).map φ).rank ↔ ∃ M ∈ Hex.Matrix.minors r A, φ M ≠ 0
theorem rank_le_iff_minors_succ_map_eq_zero (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank ≤ r ↔ ∀ M ∈ Hex.Matrix.minors (r + 1) A, φ M = 0
```

Proof: `matrixEquiv_map` rewrites the left side as the rank of
`matrixEquiv (A.map φ)`; `HexRowReduceMathlib.rank_eq` applied to
`rowReduce_isRowReduced (A.map φ)` replaces `Matrix.rank` by
`rowReduce_rank (A.map φ)`, using `Field.toGrindField` for the
`Lean.Grind.Field K` instance `rowReduce` needs and `Classical.decEq` for
`DecidableEq K`; the computational `rank_lt_iff_minors_eq_zero` then
applies, and `map_minors` moves `φ` back onto the minors of `A`. The
boundary cases need no separate treatment: for `r = 0` both sides are
false (`φ 1 = 1 ≠ 0`), and for `r > min n m` both sides are true.

The statement deliberately uses `(matrixEquiv A).map φ` rather than
`matrixEquiv (A.map φ)`, so that a consumer holding a Mathlib matrix
`B : Matrix (Fin n) (Fin m) K` and a factorisation `B = (matrixEquiv A).map φ`
rewrites once. The specialisation `φ = RingHom.id K` gives the field case:

```lean
theorem rank_lt_iff_minors_eq_zero [Field K] (A : Hex.Matrix K n m) (r : Nat) :
    (matrixEquiv A).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, M = 0
```

The same statement for a Mathlib matrix `B : Matrix (Fin n) (Fin m) R` is
obtained by `A := matrixEquiv.symm B` and `Equiv.apply_symm_apply`; the
library states that form too, as `Matrix.rank_lt_iff_minors_eq_zero'`, so
the tactic does not re-derive it.

## Specialisation bounds and rank loci

```lean
theorem rank_map_le_rank_fractionRing [IsDomain R] (φ : R →+* K) (A : Hex.Matrix R n m) :
    ((matrixEquiv A).map φ).rank ≤
      ((matrixEquiv A).map (algebraMap R (FractionRing R))).rank
```

Proof: by `le_rank_iff_exists_minor_map_ne_zero` twice. A nonzero
`φ M` forces `M ≠ 0`, and `algebraMap R (FractionRing R)` is injective on a
domain, so `algebraMap M ≠ 0`. This is the statement "no specialisation has
rank above the generic rank". The generic rank itself is computed
elsewhere (`hex-rank`, or `Hex.PolyMatrix.snfRank` in `hex-poly-smith` with
`rank_eq_ratFunc_rank` over `F[x]`) and enters only as the right side.

For polynomial matrices, over `[Field F] [DecidableEq F]` with
`[Std.TransCmp cmp] [Std.LawfulEqCmp cmp]` (the instances `HexMvPoly` and
`HexMvPolyMathlib.equiv` assume), `A : Hex.Matrix (MvPoly k F cmp) n m` and
a point `p : Fin k → F`:

```lean
theorem rankAt_lt_iff_inLocus (A) (p) (r : Nat) :
    Hex.Matrix.rankAt A p < r ↔ Hex.Matrix.InLocus r A p
theorem mem_zeroLocus_iff_rank_lt (A) (p) (r : Nat) :
    p ∈ MvPolynomial.zeroLocus F
        (Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A})) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.aeval p)).rank < r
```

Both are the headline theorem with `φ := (HexMvPolyMathlib.aeval p).toRingHom`,
the executable evaluation as an `AlgHom` (`HexMvPolyMathlib/Aeval.lean`).
`HexMvPolyMathlib.aeval_eq_eval` says its underlying function is
`MvPoly.eval p`, which is how `rankAt` and `InLocus`, defined through
`MvPoly.eval`, meet the ring-homomorphism hypothesis, and
`HexMvPolyMathlib.aeval_apply` rewrites it as `MvPolynomial.aeval p` after
`HexMvPolyMathlib.equiv`, which is how the zero-locus membership condition
meets it. `mem_zeroLocus_iff_rank_lt` uses
`MvPolynomial.zeroLocus` from `Mathlib/RingTheory/Nullstellensatz.lean`,
whose membership condition `∀ q ∈ I, aeval p q = 0` reduces to the
generators by `Ideal.span_induction`.

## Ideals and invariance

Over `[CommRing R]`, writing `I_r(A)` for
`Ideal.span {x | x ∈ Hex.Matrix.minors r A}`:

```lean
theorem span_detIdealGens_eq [DecidableEq R] (A) (r) :
    Ideal.span {x | x ∈ Hex.Matrix.detIdealGens r A} = I_r(A)
theorem span_minors_zero (A) : I_0(A) = ⊤
theorem span_minors_eq_bot_of_lt (A) (h : n < r ∨ m < r) : I_r(A) = ⊥
theorem span_minors_succ_le (A) (r) : I_(r+1)(A) ≤ I_r(A)
theorem span_minors_transpose (A) (r) : I_r(Aᵀ) = I_r(A)
theorem span_minors_mul_left_le (P : Hex.Matrix R q n) (A) (r) : I_r(P * A) ≤ I_r(A)
theorem span_minors_mul_right_le (A) (Q : Hex.Matrix R m q) (r) : I_r(A * Q) ≤ I_r(A)
theorem span_minors_mul_left_eq (P Pinv : Hex.Matrix R n n) (h : Pinv * P = identity n) (A) (r) :
    I_r(P * A) = I_r(A)
theorem span_minors_mul_right_eq (Q Qinv : Hex.Matrix R m m) (h : Q * Qinv = identity m) (A) (r) :
    I_r(A * Q) = I_r(A)
```

`span_minors_mul_left_le` is `minor_mul_left_expand` read as ideal
membership: each minor of `P * A` is a finite sum of products with minors
of `A`. `span_minors_succ_le` is the Laplace expansion
`det_eq_foldl_laplace_col` together with `deleteRowCol_selectedSubmatrix`.
The equalities follow from the two inequalities applied to `P * A` and
`Pinv * (P * A) = A`. A one-sided inverse suffices because
`Hex.Matrix.mul_eq_one_comm` makes it two-sided.

These theorems say that `I_r` is an invariant of the matrix under
invertible row and column operations. They do **not** say that `I_r` is an
invariant of the module a matrix presents: two presentation matrices of
the same module can have different shapes and are not related by
invertible square factors alone. That presentation independence is the
Fitting-ideal theorem, which this library does not prove and the pinned
Mathlib does not contain.

## The `rank_locus` tactic

`rank_locus` states, for a Mathlib matrix whose entries are ring
expressions in some atoms, exactly where its rank drops: it produces the
generators of the determinantal ideal `I_r(P)` of the reified polynomial
matrix `P`, interpreted back into the user's ring, and the theorem that
the rank of the user's matrix is below `r` if and only if every generator
vanishes. It is the tactic form of the headline theorem and adds nothing
to its mathematics. It lives here because the theorem it packages is this
library's, per [matrix-tactics §Placement](../../SPEC/matrix-tactics.md#placement);
the default threshold `r`, when the user omits it, is the generic rank of
`P`, supplied by a handler that
[hex-generic-rank-mathlib](../../SPEC/Libraries/hex-generic-rank-mathlib.md)
attaches to this library's syntax kind, so that this library does not
depend on hex-rank.

### Input and fragment

The input is reified exactly as the symbolic arm of `rank` reifies it
([hex-generic-rank-mathlib §Input classification](../../SPEC/Libraries/hex-generic-rank-mathlib.md#input-classification)):
one hex-reflect batch over all entries, sealed at `k` atoms, giving
`P : Hex.Matrix (MvPoly k C cmp) n m`, the atom valuation `v : Fin k → F`,
the coefficient interpretation `ι : C →+* F`, and the entrywise proofs
`eval₂ ι v P[i, j] = A i j`. Atoms are independent indeterminates;
nothing about their nonzeroness is assumed or asked. Closed numeric
matrices are accepted (every entry a constant, `k` possibly positive) and
give a locus statement whose generators are constants, which is correct
and useless; the diagnostic says so.

`F` is a field. A domain that is not a field is declined with the message
that its `Matrix.rank` is the rank over its fraction field
([hex-rank-mathlib §Scalar extension](../../HexRankMathlib/SPEC/hex-rank-mathlib.md#scalar-extension))
and that the tactic accepts the matrix mapped there; the extension to
domains through `rank_map_eq` is a later addition, since that theorem is
hex-rank-mathlib's and this library does not import it.

`r` is a closed natural number. The budget the batch debits is
hex-reflect's, plus one dimension this tactic adds: `minors`, the number
`n.choose r * m.choose r` of minors to enumerate, declined when exceeded
with the count in the message.

### Goal forms and outputs

The primary form introduces a hypothesis and closes nothing:

```text
rank_locus A r            -- adds h : A.rank < r ↔ ⟦g₁⟧ = 0 ∧ ⋯ ∧ ⟦gₗ⟧ = 0
rank_locus A r with h     -- names it
rank_locus A              -- r := the generic rank of P (hex-generic-rank-mathlib's handler)
```

where `g₁, …, gₗ` is `detIdealGens r P` and `⟦g⟧` is the interpretation
`eval₂ ι v g` denoted as an expression in the source atoms. The empty
conjunction is `True` (so for `r > min n m` the hypothesis reads
`A.rank < r ↔ True`), and at `r = 0` the single generator is `1`, giving
`A.rank < 0 ↔ 1 = 0`; both follow from the enumeration conventions of
[hex-determinantal-ideal §Conventions](../../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md#conventions-a-minor-of-every-size)
and need no special case.

Closing forms, each an instance of the same theorem:

| Goal | What closes it | Kernel obligation |
|---|---|---|
| `A.rank < r` | every `⟦gᵢ⟧ = 0` discharged | the full generator list |
| `A.rank ≤ r` | every generator of `I_(r+1)(P)` discharged zero | the full list at `r + 1` |
| `r ≤ A.rank` | one `⟦g⟧ ≠ 0` discharged, for a `g` the tactic names | membership of that one minor only |
| `A.rank = r` | both of the previous two | both |

Conditions are discharged in the hex-reflect order
([hex-reflect §Shared results and conditions](../../HexReflect/SPEC/hex-reflect.md#shared-results-and-conditions)):
definitional equality and local hypotheses, the configured cheap
normalisers (`norm_num` on closed propositions by default), Grind facts
when run under a Grind adapter, then side goals in tactic mode (one per
undischarged generator, in list order), otherwise decline without touching
the goal. For the lower-bound row the tactic chooses the generator to
discharge by trying the condition order on each in turn and stops at the
first success; if none succeeds it declines naming all of them. Nothing is
substituted for a goal that does not close.

The term form `rank_locus% A r` returns `{ gens, proof, poly }`: the
displayed generators, the iff, and the polynomial data (`P`, the sealed
environment, `detIdealGens r P` as `MvPoly` values) for programmatic
consumers such as the later piecewise-rank extension. The programmatic
interface returns the same record and never creates goals.

When the goal's matrix is the symbolic matrix itself, under the atom and
coefficient conditions of
[hex-generic-rank-mathlib §Output 1](../../SPEC/Libraries/hex-generic-rank-mathlib.md#output-1-generic-rank),
the term form additionally returns the ideal-level statement
`Ideal.span {g | g ∈ G'} = I_r(S)` for `G'` the generators mapped into
`MvPolynomial σ D`, and the zero-locus form
`p ∈ MvPolynomial.zeroLocus D (Ideal.span {g | g ∈ G'}) ↔ (S.map (aeval p)).rank < r`
for an explicit point variable `p`, from `mem_zeroLocus_iff_rank_lt'`
below.

### Theorems

Two generalisations of the existing statements, both in this library:

```lean
theorem rank_lt_iff_detIdealGens_map_eq_zero [CommRing R] [DecidableEq R] [Field K]
    (φ : R →+* K) (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank < r ↔ ∀ g ∈ Hex.Matrix.detIdealGens r A, φ g = 0
theorem mem_zeroLocus_iff_rank_lt' [CommRing C] [Field F] [DecidableEq C]
    (ι : C →+* F) (A : Hex.Matrix (Hex.MvPoly k C cmp) n m) (v : Fin k → F) (r : Nat) :
    (∀ g ∈ Hex.Matrix.detIdealGens r A, MvPolynomial.eval₂ ι v (HexMvPolyMathlib.equiv g) = 0) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.eval₂MathlibHom ι v)).rank < r
```

The first is `rank_lt_iff_minors_map_eq_zero` with `mem_detIdealGens_iff`
(a minor is zero or equal to a generator). The second is the first at
`φ := HexMvPolyMathlib.eval₂MathlibHom ι v`, and is the form the tactic
uses: `P` has coefficients in `C` while the user's atoms take values in
`F`, which the existing `mem_zeroLocus_iff_rank_lt` (same field for
coefficients and point) does not cover. The existing theorem is the case
`ι = RingHom.id`, `C = F`, restated through `MvPolynomial.zeroLocus`; the
`Ideal.map (MvPolynomial.map ι)` form of the zero locus for the
symbolic-matrix-itself output is stated beside it.

The lower-bound row uses `le_rank_iff_exists_minor_map_ne_zero` with the
single named minor, and needs only that minor's membership in
`minors r A`.

### Kernel route

[matrix-tactics §Kernel discipline](../../SPEC/matrix-tactics.md#kernel-discipline)
forbids evaluating `detIdealGens r P` on `Hex.Matrix (MvPoly …)` in the
kernel: the enumeration goes through `selectedColumnTuples` on `Vector`
and `Fin`, and `det` through `permutationVectors`. The kernel form is in
the Mathlib-free library
([hex-determinantal-ideal §Kernel form](../../HexDeterminantalIdeal/SPEC/hex-determinantal-ideal.md#kernel-form)):
`minorsList r L` enumerates index tuples as `List Nat` by structural
recursion and computes each minor by Laplace expansion along the first row
over the list form of `MvPoly` arithmetic, and `detIdealGensList r L`
drops zeros and duplicates. This library proves
`detIdealGensList_eq : detIdealGensList r (rows P) = detIdealGens r P`
on the values the lists denote (through hex-mv-poly-mathlib's denotation
theorem and `det_eq_foldl_laplace_col`), and the batch's quoted `P` is
identified with its row list definitionally. The kernel therefore
evaluates `detIdealGensList r L = G` for the compiled generator list `G`,
one closed equality of term lists, and each displayed `⟦gᵢ⟧` is tied to
`gᵢ` by hex-reflect's denotation proof. For the lower-bound row the kernel
evaluates one `minorList rows cols L = g` instead.

Cost is `n.choose r * m.choose r` Laplace determinants of size `r`, each
`r!` products at the realised support, the same work the compiled
enumeration did; there is no cheaper complete certificate for "these are
all the minors", and the `minors` budget bounds it.

### Prerequisite changes in other libraries

- The list form of `MvPoly` arithmetic in hex-mv-poly with its denotation
  theorem, shared with hex-generic-rank-mathlib, as that SPEC records.
- hex-reflect's denotation of a reflected polynomial value back to a
  source-ring expression with its proof `eval₂ ι v g = ⟦g⟧`, if it is not
  already exposed for values that are not batch entries; the displayed
  generators depend on it.
- The residue coefficient provider in hex-reflect-mathlib, for the
  positive-characteristic example, as hex-generic-rank-mathlib records.

### Examples

- `!![x]`, `r = 1`: `h : !![x].rank < 1 ↔ x = 0`.
- `!![x, y]`, `r = 1`: `h : !![x, y].rank < 1 ↔ x = 0 ∧ y = 0`, the exact
  locus that the conditional output of `rank` cannot give (its single
  condition is `x ≠ 0`).
- `!![x, 1; 1, x]`, `r = 2`: `h : … .rank < 2 ↔ x ^ 2 - 1 = 0`; at `r = 1`
  the generators are `x` and `1`, and `norm_num` refutes `1 = 0`, so
  `1 ≤ !![x, 1; 1, x].rank` closes by the lower-bound row with the minor
  `1` named.
- `!![1, x; 1, y]`, `r = 2`: `h : … .rank < 2 ↔ y - x = 0`.
- `!![x ^ 3 - x]` over `ZMod 3`, `r = 1`: `h : … .rank < 1 ↔ x ^ 3 - x = 0`,
  true at every point, which the statement neither knows nor needs; it
  waits on the residue provider.

### Proof probes and tests

`HexDeterminantalIdealMathlib/Tests.lean` gains the five examples above in
every goal form, the empty and `r = 0` shapes, and a decline on a matrix
over `ℤ` (a domain that is not a field). Proof probes under
`bench/HexDeterminantalIdealMathlib/ProofProbe` record, as fresh-module
evidence with matched baselines, batch reification, compiled enumeration,
kernel time of `detIdealGensList`, and total elaboration, on the
`symbolic` family of [hex-generic-rank §Benchmarking](../../SPEC/Libraries/hex-generic-rank.md#benchmarking)
restricted to `r ≤ 3`. There is no Mathlib comparator (no Lean tactic
states a rank locus), declared as
**no-comparable-surface-in-named-comparator**; the report is
`reports/hex-determinantal-ideal-mathlib-performance.md` with absolute
numbers and preregistered ceilings. The library therefore drops
`correspondence_only` in `libraries.yml` and gains `proof_probes`, and its
dependencies gain `HexReflect`, `HexReflectMathlib` and
`HexMatrixMathlib`.

### What this tactic does not do

It does not reduce the generator list: no Gröbner basis, no radical, no
decomposition into components, no sign or leading-coefficient
normalisation beyond `detIdealGens`'s dropping of zeros and duplicates.
Those are the Gröbner-basis work that is out of scope for this round, and
when it exists it consumes this tactic's `poly` field. It does not decide
whether the locus is empty, nonempty, or everything; over a finite field
the last is common and the statement is still correct pointwise.

## Tests

`HexDeterminantalIdealMathlib/Tests.lean`, build-only, no runtime checks:

- `rank_lt_iff_minors_map_eq_zero` on a closed `Hex.Matrix ℤ 2 3` through
  `Int.castRingHom ℚ`, both at `r = 2` (nonzero minor, rank `2`) and at
  `r = 3` (empty list, rank below `3`), with the minors read off through
  `det_two_by_two` once the tuple enumeration is evaluated by `rfl` (the
  Leibniz sum is not kernel-evaluated from a `module` file, since
  `permutationVectors` goes through core `Vector.map`, which the kernel
  cannot unfold there) and the rank rewritten through the theorem;
- `rankAt_lt_iff_inLocus` on the `2 × 2` Vandermonde matrix in two
  indeterminates over `ℚ`, at `(1, 1)` (in the locus at `r = 2`) and at
  `(1, 2)` (not in the locus);
- `span_minors_mul_left_eq` on a `2 × 2` unimodular `P` and a closed `A`,
  to check that the hypotheses are stated in the form a consumer has.
