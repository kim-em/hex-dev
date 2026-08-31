# hex-poly-smith-mathlib

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexPolySmith`
Computational performance owner: `HexPolySmith`

`hex-poly-smith-mathlib` is the Mathlib correspondence layer for
`hex-poly-smith`. It depends on `hex-poly-smith`, `hex-poly-mathlib`,
and `hex-matrix-mathlib`.

The library owns no executable Smith algorithm, reifier, checker, or tactic.
It transports the Mathlib-free result to `Polynomial F`, constructs Mathlib's
Smith-basis structure, decomposes the presented quotient module, and identifies
the executable rank with rank over `RatFunc F`.

## Public API

The user-facing namespace is `HexPolySmithMathlib`.

```lean
def polyMatrixEquiv (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin n) (Fin m) (Polynomial F)

theorem polyMatrixEquiv_apply (A : Hex.Matrix (DensePoly F) n m)
    (i : Fin n) (j : Fin m) :
    polyMatrixEquiv A i j = HexPolyMathlib.toPolynomial A[(i, j)]
theorem polyMatrixEquiv_add (A B : Hex.Matrix (DensePoly F) n m) :
    polyMatrixEquiv (A + B) = polyMatrixEquiv A + polyMatrixEquiv B
theorem polyMatrixEquiv_mul (A : Hex.Matrix (DensePoly F) n m)
    (B : Hex.Matrix (DensePoly F) m k) :
    polyMatrixEquiv (A * B) = polyMatrixEquiv A * polyMatrixEquiv B

theorem monicize_eq_normalize (p : DensePoly F) :
    HexPolyMathlib.toPolynomial (DensePoly.monicize p) =
      normalize (HexPolyMathlib.toPolynomial p)

theorem evaluationSeparatesUpTo_of_nodup
    (pts : Vector F k) (bound : Nat)
    (hpts : pts.toList.Nodup) (hcard : bound < k) :
    EvaluationSeparatesUpTo pts bound

noncomputable def smithNormalForm (A : Hex.Matrix (DensePoly F) n m) :
    Module.Basis.SmithNormalForm
      (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)))
      (Fin m) (snfRank A)

theorem smithNormalForm_chain (A : Hex.Matrix (DensePoly F) n m)
    (i : Nat) (h : i + 1 < snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣
      (smithNormalForm A).a ⟨i + 1, h⟩

noncomputable def quotientEquiv (A : Hex.Matrix (DensePoly F) n m) :
    ((Fin m → Polynomial F) ⧸
        Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)))
      ≃ₗ[Polynomial F]
    (Fin (m - snfRank A) → Polynomial F) ×
      ⨁ i : Fin (snfRank A),
        Polynomial F ⧸ Ideal.span
          {HexPolyMathlib.toPolynomial ((invariantFactors A)[i])}

theorem rank_eq_ratFunc_rank (A : Hex.Matrix (DensePoly F) n m) :
    snfRank A =
      ((polyMatrixEquiv A).map
        (algebraMap (Polynomial F) (RatFunc F))).rank
```

`smithNormalForm_a_snfData` identifies Mathlib's basis coefficients with the
executable diagonal, and `smithNormalForm_f_val` states that its embedding uses
the first `snfRank A` ambient coordinates. `smithNormalForm_chain` adds the
canonical divisibility order that Mathlib's simultaneous-basis structure does
not itself carry.

`quotientEquiv` presents the quotient as its free part and cyclic torsion
summands. Unit factors are harmless zero summands at this theorem level; the
Mathlib-free `moduleStructure` projection removes them for executable output.

## Verification ownership

This is a correspondence-only layer. It has no conformance module, benchmark
driver, or performance report. Runtime behavior transported by this library is
covered by `HexPolySmith.Conformance`; performance belongs to
`hex-poly-smith`. Building `HexPolySmithMathlib` checks every correspondence
proof and the manual's worked use of the API.

The layer's Phase 4 classification is `correspondence-only-layer`, with
`hex-poly-smith` as its computational performance owner.

## Files

- `Equiv.lean`: entrywise polynomial-matrix transport and normalization.
- `Basis.lean`: Mathlib `Module.Basis.SmithNormalForm` construction.
- `Chain.lean`: invariant-factor coefficient and divisibility-chain theorems.
- `Quotient.lean`: free-plus-torsion quotient decomposition.
- `Rank.lean`: rank after extension of scalars to `RatFunc F`.
