# hex-hermite-theory (depends on hex-hermite + hex-row-reduce-theory + Mathlib)

The Mathlib correspondence layer for the executable, Mathlib-free integer
Hermite normal form in
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md). It identifies the row
lattice, rank, membership decision, transform, and kernel basis computed by
`hex-hermite` with Mathlib's linear-algebra objects. All computation remains in
the core library.

## Scope

The layer owns correspondence and the `hermite` frontend; its producer and
list checker remain in HexHermite.

Its public surface is:

```lean
theorem span_hnf (A : Hex.Matrix Int n m) :
    Submodule.span ℤ (Set.range (matrixEquiv (Hex.Matrix.hnf A))) =
      Submodule.span ℤ (Set.range (matrixEquiv A))

theorem isUnit_transform (A : Hex.Matrix Int n m) :
    IsUnit (matrixEquiv (Hex.Matrix.hnfData A).transform)

theorem hnfRank_eq_rank (A : Hex.Matrix Int n m) :
    Hex.Matrix.hnfRank A = (matrixEquiv A).rank

theorem latticeContains_iff_mem (A : Hex.Matrix Int n m)
    (v : Vector Int m) :
    Hex.Matrix.latticeContains A v = true ↔
      vectorEquiv v ∈
        Submodule.span ℤ (Set.range (matrixEquiv A))

noncomputable def kernelBasis (A : Hex.Matrix Int n m) :
    Basis (Fin (n - Hex.Matrix.hnfRank A)) ℤ
      (LinearMap.ker (_root_.Matrix.vecMulLinear (matrixEquiv A)))
```

The supporting public declarations expose the two intermediate
characterisations used by those headlines:

- `mem_span_iff` identifies Mathlib span membership with the core
  `Matrix.memLattice` proposition;
- `kernelVector`, `kernelRows_independent`, `kernelVector_independent`, and
  `kernelVector_spans` package the executable kernel rows as an independent
  spanning family;
- `kernelBasis_apply` states that the resulting Mathlib basis evaluates
  to the corresponding row of `Hex.Matrix.kernelBasis`.

No theorem about the executable representation itself belongs here. HNF
existence, uniqueness, idempotence, lattice preservation, membership
soundness/completeness, and kernel soundness/completeness/independence remain
in `hex-hermite`.

## Correspondence contracts

`span_hnf` says the canonical HNF presentation generates exactly the input row
lattice. `isUnit_transform` strengthens the core inverse witnesses into
Mathlib's unit interface. `hnfRank_eq_rank` identifies the executable count of
nonzero HNF rows with Mathlib's noncomputable matrix rank.

`latticeContains_iff_mem` is the Boolean-to-proposition boundary: the core
decision procedure returns true exactly for vectors in the Mathlib span of the
input rows.

`kernelBasis` is the constructive payoff. Mathlib can obtain a basis of a
submodule of a free module noncomputably; this declaration instead packages
the rows computed by `Hex.Matrix.kernelBasis`, with independence and spanning
proved in Lean. Its index type has the executable nullity
`n - Hex.Matrix.hnfRank A`.

## Verification

For the existing correspondence, Phase 3 is established by auditing
the executable coverage in `hex-hermite`, without a separate runtime Mathlib
conformance module. The frontend additionally requires the build-only proof
tests below:

- HNF form and transform checks cover `span_hnf` and `isUnit_transform`;
- rank-deficient cases cover `hnfRank_eq_rank`;
- lattice members and residual non-members cover
  `latticeContains_iff_mem`;
- kernel soundness and bounded independence checks cover the executable data
  transported by `kernelBasis`.

Theorems in this library are checked by the kernel in the ordinary library
build and by the pair's Mathlib lint regression.

## External comparators

The computational performance owner is `hex-hermite`; its benchmark target
carries the evidence for HNF, rank, lattice membership and kernel extraction.
The tactic adds a proof-performance track, without a
Mathlib-importing benchmark executable.

## Frontend implementation and validation

The frontend lives in `HexHermiteTheory/Tactic.lean`; list certificates belong to
`HexHermite/Kernel.lean`, and the companion's soundness theorems accept arbitrary
checked witnesses. Proof tests live in `HexHermiteTheory/Tests.lean`; malformed
certificate regressions also belong in the Mathlib-free conformance driver.

Representative example files under `bench/HexHermiteTheory/ProofProbe` exercise
tall and empty kernel bases, membership and nonmembership. CI builds them
through `HexStructuralTacticProofProbe` on every PR. These examples and the
ordinary library/conformance tests establish correctness; this proof surface has
no paired timing decision, timing ladder, absolute build-time gate, profile or
headline-report requirement. The computational owner's LeanBench obligations
remain separate.


## The `hermite` tactic

The frontend follows [the matrix tactic protocol](../../SPEC/matrix-tactics.md)
and [the `rank` template](../../HexRankTheory/SPEC/hex-rank-theory.md#the-rank-tactic).
The list certificate and producer belong to HexHermite, with Mathlib transport
and the frontend here. The existing `HexHermiteTheory/Kernel.lean` proves
kernel-basis correspondence; extend it or use a separate certificate module
without displacing that API.

### Goals, result and carriers

Declare non-reserved `hermite` and term form `hermite% A`. Accept closed
integer `A : Matrix (Fin n) (Fin m) ℤ`. Write
`L(A) := Submodule.span ℤ (Set.range A)` in this section. Supported goals are
`v ∈ L(A)`, `v ∉ L(A)` for a closed integer vector, and a basis goal
`Basis (Fin r) ℤ L(A)` with a stated closed rank `r` (also its `Nonempty`
wrapper). A basis goal constructs the canonical nonzero HNF rows; it is
not an equality to an arbitrarily chosen noncomputable basis.

The new term record `HermiteResult A` exposes `rank`, `rank_le : rank ≤ min n m`,
`form : Matrix (Fin n) (Fin m) ℤ`, an HNF proof, `span : L(form) = L(A)`,
`basis : Basis (Fin rank) ℤ L(A)`, and a theorem that the underlying vector
of `basis i` is row `i` of `form` (using `rank_le` for its row index).
The HNF proof is the existing `Hex.Matrix.IsHNF` on decoded data, transported
through `matrixEquiv`; the record retains the checked pivots and transforms
needed to state it. Values are literals, with no dependent dimension computed
by reducing `hnfRank A`. This is the row-lattice basis from `hnfBasis`,
not `HexHermiteTheory.kernelBasis`, whose vectors live in `Fin n → ℤ`
and describe the left kernel instead.

Use [the shared literal layer](../../HexMatrixTheory/SPEC/hex-matrix-theory.md#matrix-literals).
Request against its SPEC the closed integer vector adapter for `v` and its
`vecOfList` identification. Matrix recognition and supported unfolding stay
with that layer. Noninteger and symbolic coefficients are outside this arm.

### Kernel certificate and soundness

Existing `Hex.Matrix.hnfCert A H U W r piv` in `HexHermite/Cert.lean`
checks `U * A = H`, `U * W = I`, and `isHNFForm H r piv`.
`hnfCert_sound` concludes `IsHNF A ⟨r, H, U, piv⟩` for arbitrary accepted
data. It derives the reverse inverse over square integer matrices; that is
not an extra producer hypothesis. Its packed matrix checker is a reference
form, not a suitable reduction path for the tactic.

Require `HermiteWitness`/`checkHermiteList` in HexHermite with row lists for
`H`, `U`, `W`, a natural rank and a list of natural pivot columns. Check
exact dimensions, rank bounds, pivot count/range/strict order, positive
leading pivots, leading and below-pivot zeros, zero trailing rows, and the
bounds `0 ≤ entry < pivot` above each pivot, as well as both displayed
products. All arithmetic is exposed structural recursion on lists of
`Int`/`Nat`, with no `Hex.Matrix`, `Array`, `Vector`, `Fin`, `Finset` or
well-founded recursion on the reduction path. Do not run HNF elimination.

For membership, augment the certificate with an integer coefficient list
`q` of length `r` and residual `t` of length `m`, verifying
`v = q * H.take r + t` and `0 ≤ t[piv i] < H[i,piv i]` for every pivot.
The producer obtains these by the ordinary left-to-right HNF remainder
calculation; the kernel only checks the identity and bounds. A zero residual
certifies membership. A nonzero residual certifies nonmembership: if it were
in the row lattice, its first nonzero pivot coefficient would make a pivot
coordinate a nonzero multiple of the positive pivot, contradicting the
bounds; successively zero coefficients force the whole residual to zero.
This also covers a residual supported only in nonpivot columns and rank zero.

Require new `hermite_of_checkList` to establish the record's HNF, span and
basis properties from the Boolean check and `hA : A = ofLists n m rows`.
The proof decodes to `hnfCert_sound`, then transports the arbitrary witness.
Existing `span_hnf`, `hnfRank_eq_rank` and `latticeContains_iff_mem` in this
companion are about the canonical producer output; they cannot be applied
by evaluating `hnf A` or `latticeContains A v` in the kernel. Extend their
proofs to checked `IsHNF` data, using the same membership equivalence as
`latticeContains_iff_mem`, and add a list-remainder soundness theorem with
both membership outcomes. For the basis, lattice preservation and zero
trailing rows prove spanning, while strictly increasing positive pivots
prove independence. Membership alone is insufficient to construct a basis.
These arbitrary-witness and list-remainder bridges are new obligations,
not claims that the existing canonical correspondence already accepts lists.

Required API schemata (all new; proof fields supplement the prose contract):

```lean
-- HexHermite/Kernel.lean, namespace Hex.Matrix
structure HermiteWitness where
  rank : Nat
  pivots : List Nat
  form transform inverse : List (List Int)

def checkHermiteList (n m : Nat) (rows : List (List Int))
    (c : HermiteWitness) : Bool

-- HexHermiteTheory/Certificate.lean (re-exported by Kernel.lean), namespace HexHermiteTheory
structure HermiteResult {n m : Nat} (A : Matrix (Fin n) (Fin m) ℤ) where
  rank : Nat
  rank_le : rank ≤ min n m
  form : Matrix (Fin n) (Fin m) ℤ
  inputRows : List (List Int)
  input_eq : A = HexMatrixTheory.ofLists n m inputRows
  witness : Hex.Matrix.HermiteWitness
  rank_eq : rank = witness.rank
  form_eq : form = HexMatrixTheory.ofLists n m witness.form
  checked : Hex.Matrix.checkHermiteList n m inputRows witness = true
  span : Submodule.span ℤ (Set.range form) = Submodule.span ℤ (Set.range A)
  basis : Module.Basis (Fin rank) ℤ (Submodule.span ℤ (Set.range A))
  basis_row : ∀ i : Fin rank,
    (basis i : Fin m → ℤ) = form ⟨i.val, lt_of_lt_of_le i.isLt
      (le_trans rank_le (Nat.min_le_left n m))⟩

noncomputable def hermite_of_checkList {n m : Nat}
    (A : Matrix (Fin n) (Fin m) ℤ) (rows : List (List Int))
    (c : Hex.Matrix.HermiteWitness)
    (hA : A = HexMatrixTheory.ofLists n m rows)
    (hc : Hex.Matrix.checkHermiteList n m rows c = true) : HermiteResult A
```

The record stores checked HNF data rather than requiring an equality to the
output of `hnf`; `hnfCert_sound` supplies its `IsHNF` property without
producer replay. Constructor projection theorems fix `rank` and `form` to
the witness. Membership soundness takes this checked witness plus the
coefficient/residual list checks and concludes `v ∈ L(A) ↔ residual = 0`.

### Producer and proof assembly

Use compiled `Hex.Matrix.hnfWithInv`, which retains both transforms
in `HermiteData`, reshape its `hnfCert` data, and compute membership remainder
data only when needed. Re-check the complete list certificate before quoting.
Following `HexRankTheory/Kernel.lean` and `Tactic.lean`, keep decoding and
transport in proved lemmas, use the shared literal identification, and check
all certificate propositions in one synchronous auxiliary theorem. Construct
the basis/term record from that theorem; do not pass a `Basis` type itself
to `HexMatrixTheory.Literal.addClosedProof`. There is no preliminary kernel evaluation of the check.

Use the shared four outcomes: other operations/carriers are `notApplicable`,
in-fragment capability/budget limits are `declined`, accepted proofs are
`success`, and bad certificates/kernel rejections are `failure`. A false
membership target reports the certified nonzero residual; a false
nonmembership target reports the coefficients, and a wrong basis dimension
reports the rank. Preserve the user's proposition and diagnose rejection
without replaying `hnf` or `latticeContains`.

### Conformance and proof probes

Test both membership outcomes, basis construction and its row equations,
term mode, every literal route, zero and empty shapes, tall/wide matrices,
non-leading pivots and negative inputs. Refute incorrect transform products,
inverses, dimensions, duplicate/out-of-range pivots, negative pivots,
nonzero trailing rows, out-of-range above-pivot entries, corrupted remainder
identities and residual bounds. Include nonmembership supported in a nonpivot
column and a valid noncanonical transform. Audit all accepted proof axioms
against `propext`, `Classical.choice`, `Quot.sound` only.

The CI example coverage is specified in [Frontend implementation and validation](#frontend-implementation-and-validation).
