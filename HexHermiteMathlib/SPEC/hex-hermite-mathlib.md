# hex-hermite-mathlib (depends on hex-hermite + hex-row-reduce-mathlib + Mathlib)

The Mathlib correspondence layer for the executable, Mathlib-free integer
Hermite normal form in
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md). It identifies the row
lattice, rank, membership decision, transform, and kernel basis computed by
`hex-hermite` with Mathlib's linear-algebra objects. All computation remains in
the core library.

## Scope

This layer owns correspondence only. It has no executable reifier,
certificate checker, tactic, conformance target, benchmark target, or proof
performance probe of its own.

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

This is a correspondence-only layer, so Phase 3 is established by auditing
the executable coverage in `hex-hermite`, not by adding a ceremonial Mathlib
conformance module:

- HNF form and transform checks cover `span_hnf` and `isUnit_transform`;
- rank-deficient cases cover `hnfRank_eq_rank`;
- lattice members and residual non-members cover
  `latticeContains_iff_mem`;
- kernel soundness and bounded independence checks cover the executable data
  transported by `kernelBasis`.

Theorems in this library are checked by the kernel in the ordinary library
build and by the pair's Mathlib lint regression.

## External comparators

`correspondence-only-layer`: this library has zero benchmark targets because
it owns no computational or proof-search surface. Its computational
performance owner is `hex-hermite`; that library's benchmark target carries
the evidence for HNF, rank, lattice membership, and kernel extraction.
