# hex-smith-mathlib

## Correspondence-only classification

The existing API is a `correspondence-only-layer`; the specified `smith`
frontend adds conformance and a fresh-module proof-performance track when
implemented.

Computational conformance owner: `HexSmith`
Computational performance owner: `HexSmith`

`hex-smith-mathlib` is the Mathlib correspondence layer for the executable
integer Smith normal form in `hex-smith`. It imports Mathlib; `hex-smith`
remains Mathlib-free.

## API

```lean
noncomputable def smithNormalForm (A : Hex.Matrix Int n m) :
    Module.Basis.SmithNormalForm (rowSpan A) (Fin m)
      (Hex.Matrix.snfRank A)

theorem smithNormalForm_chain (A : Hex.Matrix Int n m) (i : Nat)
    (h : i + 1 < Hex.Matrix.snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣
      (smithNormalForm A).a ⟨i + 1, h⟩

theorem snfRank_eq_rank (A : Hex.Matrix Int n m) :
    Hex.Matrix.snfRank A = (matrixEquiv A).rank

noncomputable def quotientEquiv (A : Hex.Matrix Int n m) :
    ((Fin m → ℤ) ⧸ rowSpan A) ≃ₗ[ℤ]
      (Fin (m - Hex.Matrix.snfRank A) → ℤ) ×
        ⨁ i : Fin (Hex.Matrix.snfRank A),
          ℤ ⧸ Ideal.span
            ({(Hex.Matrix.invariantFactors A)[i]} : Set ℤ)
```

The ambient basis is the row basis of the recorded inverse right transform.
The relation basis is formed by the independent rows of the left-transformed
presentation. The defining basis identity has coefficients exactly equal to
the executable invariant factors, so the chain theorem comes from
`Hex.Matrix.invariantFactors_chain` rather than Mathlib's noncomputable PID
existence proof.

`snfRank_eq_rank` is the consumer-facing rank corollary, in `HexSmithMathlib.Rank`.
It composes the Mathlib-free `Hex.Matrix.snfRank_eq_hnfRank` with the
Hermite-to-Mathlib bridge `HexHermiteMathlib.hnfRank_eq_rank`, so it belongs
here rather than in `HexSmith`; the module imports `HexHermiteMathlib.Rank`,
which the `HexHermiteMathlib.Span` chain the rest of this library uses does not
reach.

The quotient equivalence is rank-general. In ambient Smith coordinates its
map keeps the final `m - snfRank A` coordinates as the free factor and reduces
each leading coordinate modulo its invariant factor. Its kernel is proved to
be exactly `rowSpan A`, and explicit coordinate representatives prove
surjectivity. This avoids Mathlib's helper for full-rank submodules, which
cannot represent the free complement.

The authoritative algorithm, correctness, uniqueness, conformance, and
benchmark requirements shared with this layer are in
[`SPEC/Libraries/hex-smith.md`](../../SPEC/Libraries/hex-smith.md).

## Runtime boundary

The existing `hex-smith-mathlib` correspondence owns no independent
executable algorithm. Its computable projections, such as
`relationVector`, only expose data computed by `HexSmith`; the remaining
declarations are correspondence proofs checked by the kernel in the ordinary
`HexSmithMathlib` build.

For the correspondence API, `HexSmith` is the computational performance
owner. The tactic below requires its own proof probes and report when
implemented, while introducing no Mathlib-importing benchmark executable.

## The `smith` tactic

This is a required extension following
[the matrix tactic protocol](../../SPEC/matrix-tactics.md) and
[the `rank` template](../../HexRankMathlib/SPEC/hex-rank-mathlib.md#the-rank-tactic).
The certificate producer/checker belong to HexSmith; Mathlib transport and
the frontend belong here. `invariant_factors` remains reserved for the future
hex-invariant-factors library.

### Goals, result and carriers

Declare the non-reserved atom `smith` and term form `smith% A`. Initially
accept closed `A : Matrix (Fin n) (Fin m) ℤ`. For this section abbreviate
`L(A) := Submodule.span ℤ (Set.range A)`. Rows are relations, so the
presented cokernel is `(Fin m → ℤ) ⧸ L(A)`, equivalently the cokernel of
`Matrix.vecMulLinear A`, not the cokernel of `A.mulVecLin`.

Choose the `quotientEquiv`-shaped goal, with stated closed rank `r` and
closed factors `d : Fin r → ℤ`:

```text
((Fin m → ℤ) ⧸ L(A)) ≃ₗ[ℤ]
  (Fin (m - r) → ℤ) × ⨁ i : Fin r, ℤ ⧸ Ideal.span ({d i} : Set ℤ)
```

`by smith` constructs that equivalence; also accept its `Nonempty` wrapper.
Require `r ≤ min n m`, positive factors in divisibility order, including
unit factors; zeros describe the free complement and are not listed in `d`.
Compare the certified factors exactly with the target. Isomorphic quotients
with noncanonical alternative presentations are outside this tactic's goal
normalization. This choice exposes both torsion and free coordinates and
avoids asking users to specify nonunique ambient/relation bases.

The new dependent term record `SmithResult A` contains `rank : Nat`,
`rank_le : rank ≤ min n m`, `factors : Fin rank → ℤ`, positivity and
adjacent divisibility proofs, and `equiv` of the displayed type using these
fields. Its values are quoted lists read as functions, never reductions of
`snfRank A` or `invariantFactors A`. The empty and rectangular cases retain
the full free complement; a unit factor contributes the zero quotient.

Use [hex-matrix-mathlib's literal layer](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#matrix-literals).
Request against its SPEC a closed vector literal adapter for the stated
factor function, with identification by `vecOfList`; do not duplicate it.
An explicitly optional `F[x]` arm belongs to HexPolySmithMathlib, attaches a
handler to this same syntax kind, and uses HexPolySmith's polynomial SNF
certificate over `[Lean.Grind.Field F] [DecidableEq F]`. It must transport to
Mathlib `Polynomial F` under coherent Mathlib field instances, use monic
nonzero factors and exact coefficient-list identities, and supply its own
arbitrary-certificate quotient bridge and proof evidence. The integer arm
acquires no HexPolySmith dependency. This optional arm is not an assertion
that the current polynomial companion already provides that bridge.

### Kernel certificate and soundness

Existing `Hex.Matrix.snfCert A S T` in `HexSmith/Cert.lean` checks
`T = S.left * A`, `T * S.right = diagMatrix S.diag n m`, both recorded
right-inverse identities, and SNF shape. `snfCert_sound` concludes
`IsSNF A S` for any accepted `SmithData n m`, with no producer hypothesis.
Its current packed `mulEqCert` route still reads `Hex.Matrix`; do not reduce
that reference checker in a tactic proof.

Require new `SmithWitness`/`checkSmithList` in HexSmith: rank, positive
diagonal list, row lists for `left`, `leftInv`, `right`, `rightInv`, and
`T`. Check all exact shapes and rank bounds, the four product identities,
positivity and adjacent divisibility. Structural list products over `Int`
are the initial checker; the second product may transpose lists as the
reference checker does. The kernel never runs Smith reduction, pivot search,
GCD, or a packed matrix access. All reduction-path definitions are exposed
structural recursions over list/`Nat`/`Int`, without `Array`, `Vector`, `Fin`,
`Finset`, `Hex.Matrix` or well-founded recursion.

The required new `smith_of_checkList` transports acceptance at input rows
`L` to a `SmithResult (ofLists n m L)`, with rank/factors fixed to the
witness, and a wrapper accepts `hA : A = ofLists n m L`. Establish the
reference check and apply `snfCert_sound` in the proof of this bridge.
Then generalize the constructions in `HexSmithMathlib/Basis.lean` and
`Quotient.lean` to arbitrary `S` with `IsSNF A S`. Their existing
`smithNormalForm`, `smithNormalForm_chain` and `quotientEquiv` take `A` and
use `snfData A`; they are not already arbitrary-certificate transports.
The new bridge uses the supplied inverse right transform for ambient
coordinates and the supplied left transform for relations. The inverse
identities prove unimodularity, and the diagonal identity proves the kernel
and surjectivity facts needed for the quotient equivalence. No reduction or
equality proof of the producer's transforms is permitted; transforms need
not be canonical even when factors are. The divisibility proof comes from
the checked shape, rather than replaying `smithNormalForm_chain A`.

### Producer and proof assembly

Run compiled `snfData` once (the data-producing counterpart of `snf`), form
`T`, convert the reference certificate to `SmithWitness`, and re-check with
`checkSmithList` before quotation. As in `HexRankMathlib/Kernel.lean` and
`Tactic.lean`, separate list-to-Mathlib soundness, literal identification,
and frontend assembly. All proof fields use one synchronous auxiliary
theorem certifying the witness; build the equivalence as data from those
fields, since `mkAuxTheorem` certifies propositions, not a linear equivalence
itself. Do not kernel pre-check and then check again.

Different operations/carriers are `notApplicable`; an in-fragment missing
adapter or exceeded budget is `declined`. A mismatching target reports the
computed rank and factors; a rejected producer witness or kernel proof is
`failure`. Unimodular transforms cannot be silently replaced to force a
target match. Follow the shared diagnostic and axiom protocol.

### Conformance and proof probes

Test the equivalence and `Nonempty` forms and every term-record proof, all
literal routes, zero matrices, `0 × m`, `n × 0`, full rank, rectangular and
rank-deficient presentations, units, negative input entries and false target
factors. Refute malformed certificates by corrupting each transform/inverse
product, `T`, dimensions, rank, diagonal positivity or divisibility. Include
a noncanonical but valid transform certificate to ensure soundness does not
assume producer equality. Audit axioms against `propext`, `Classical.choice`,
`Quot.sound` only.

On implementation reserve `bench/HexSmithMathlib/ProofProbe`. Named families:
`chain-conjugate` (unimodular transforms of positive divisibility chains),
`rectangular-presentation` (`n × 2n` and `2n × n`), `rank-deficient`
(rank `n / 2`), and `large-coefficients`; dimensions `2, 4, 8, 16`, input
heights `8, 32`, and `64, 256` bits for the last family. Include factors
`1` and nontrivial free summands. With no Mathlib tactic comparator, record
absolute fresh-module times/medians, baseline deltas and one kernel-only
profile per family, not a speedup ratio. Use six samples paired adjacently
with import-only baselines, alternating orientation, per
[SPEC/benchmarking.md](../../SPEC/benchmarking.md#fresh-module-proof-evidence).
Record certificate entry counts, serialized bytes, maximum integer height,
emitted artifact sizes, axiom sets and complete source/toolchain/host
provenance; retain every completed sample and report timeouts. Preregister
operational caps. Ordinary compiled performance remains HexSmith's concern.
