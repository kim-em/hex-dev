/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib.Rank
public import HexMvPolyMathlib
public import Mathlib.RingTheory.Nullstellensatz

public section

/-!
Rank loci of polynomial matrices. Both theorems are the headline theorem of
`Rank` with `φ` the executable evaluation `HexMvPolyMathlib.aeval p` as a
ring homomorphism: `rankAt_lt_iff_inLocus` reads it through `MvPoly.eval`,
which is how the executable `rankAt` and `InLocus` are defined, and
`mem_zeroLocus_iff_rank_lt` reads it through `MvPolynomial.aeval` after
`HexMvPolyMathlib.equiv`, which is how membership in `MvPolynomial.zeroLocus`
is stated.
-/

namespace HexDeterminantalIdealMathlib

open HexMatrixMathlib

universe u

variable {k : Nat} {F : Type u} [Field F] [DecidableEq F]
  {cmp : Hex.Mono k → Hex.Mono k → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  {n m : Nat}

/-- The evaluation algebra homomorphism is `MvPoly.eval` as a function. -/
private theorem coe_aeval_eq_eval (p : Fin k → F) :
    (⇑(HexMvPolyMathlib.aeval p).toRingHom : Hex.MvPoly k F cmp → F) = Hex.MvPoly.eval p := by
  funext q
  exact HexMvPolyMathlib.aeval_eq_eval p q

/-- The rank of a polynomial matrix at a point is below `r` exactly when the
point lies in the zero set of `I_r(A)`. -/
theorem rankAt_lt_iff_inLocus (A : Hex.Matrix (Hex.MvPoly k F cmp) n m) (p : Fin k → F)
    (r : Nat) :
    Hex.Matrix.rankAt A p < r ↔ Hex.Matrix.InLocus r A p := by
  have h := rank_lt_iff_minors_map_eq_zero (HexMvPolyMathlib.aeval p).toRingHom A r
  rw [coe_aeval_eq_eval, ← matrixEquiv_map] at h
  rw [Hex.Matrix.inLocus_iff, Hex.Matrix.rankAt_eq,
    show Hex.Matrix.rowReduce_rank (Hex.Matrix.specialize A p) =
      (Hex.Matrix.rowReduce (A.map (Hex.MvPoly.eval p))).rank from rfl,
    rank_eq (Hex.Matrix.rowReduce_isRowReduced _)]
  exact h

/-- The zero set of `I_r(A)` is the locus where the rank drops below `r`. -/
theorem mem_zeroLocus_iff_rank_lt (A : Hex.Matrix (Hex.MvPoly k F cmp) n m) (p : Fin k → F)
    (r : Nat) :
    p ∈ MvPolynomial.zeroLocus F
        (Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A})) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.aeval p)).rank < r := by
  rw [MvPolynomial.mem_zeroLocus_iff,
    show (matrixEquiv A).map (HexMvPolyMathlib.aeval p) =
      (matrixEquiv A).map (HexMvPolyMathlib.aeval p).toRingHom from rfl,
    rank_lt_iff_minors_map_eq_zero]
  constructor
  · intro h M hM
    have hq := h (HexMvPolyMathlib.equiv M) (Ideal.subset_span ⟨M, hM, rfl⟩)
    rw [HexMvPolyMathlib.equiv_apply, ← HexMvPolyMathlib.aeval_apply] at hq
    exact hq
  · intro h q hq
    have hle : Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A}) ≤
        RingHom.ker (MvPolynomial.aeval p : MvPolynomial (Fin k) F →ₐ[F] F) := by
      rw [Ideal.span_le]
      rintro _ ⟨M, hM, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, HexMvPolyMathlib.equiv_apply,
        ← HexMvPolyMathlib.aeval_apply]
      exact h M hM
    exact RingHom.mem_ker.mp (hle hq)

end HexDeterminantalIdealMathlib
