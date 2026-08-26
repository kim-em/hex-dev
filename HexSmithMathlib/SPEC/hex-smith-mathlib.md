# hex-smith-mathlib

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

`hex-smith-mathlib` owns no executable reifier, certificate checker, tactic,
or other runtime surface. Its declarations are correspondence proofs checked
by the kernel in the ordinary `HexSmithMathlib` build. All executable data it
transports is owned by `hex-smith`.
