/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.LiteralIsolations

public section

/-! Small proof-level regression tests for literal-chain replay. -/

open Polynomial

namespace HexRealRootsMathlib.LiteralChainTests

private noncomputable def quad : Polynomial ℝ := X ^ 2 - 1

private theorem replay : Sturm.Replay quad X [1] := by
  apply Sturm.Replay.cons
  · change ∃ left quotient right, 0 < left ∧ 0 < right ∧ _
    refine ⟨1, X, 1, by norm_num, by norm_num, ?_⟩
    simp [quad, pow_two]
  · exact Sturm.Replay.pair isUnit_one

private theorem nonzero : ∀ q ∈ [quad, X, 1], q ≠ 0 := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro h
    have heval := congrArg (Polynomial.eval (0 : ℝ)) h
    norm_num [quad] at heval
  · exact Polynomial.X_ne_zero
  · exact one_ne_zero

example : Sturm.IsSturmChain quad [quad, X, 1] := by
  apply Sturm.isChain_of_replay replay nonzero 2 (by norm_num)
  simp [quad, Polynomial.derivative_pow]

example : Squarefree quad := by
  apply Sturm.squarefree_of_replay replay 2 (by norm_num)
  simp [quad, Polynomial.derivative_pow]

/-! The integer replay below has four entries, so it exercises both supplied
triple identities as well as the list-to-array count bridge. -/

private def zf : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]

private def zs₁ : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[(-1 : Int), 0, 3]

private def zs₂ : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[(0 : Int), 1]

private def zs₃ : Hex.ZPoly :=
  Hex.DensePoly.ofCoeffs #[(1 : Int)]

private theorem zreplay : ZReplay zf zs₁ [zs₂, zs₃] := by
  apply ZReplay.cons
  · change ∃ left quotient right, 0 < left ∧ 0 < right ∧ _
    refine ⟨3, Hex.DensePoly.ofCoeffs #[(0 : Int), 1], 2,
      by decide, by decide, by decide⟩
  · apply ZReplay.cons
    · change ∃ left quotient right, 0 < left ∧ 0 < right ∧ _
      refine ⟨1, Hex.DensePoly.ofCoeffs #[(0 : Int), 3], 1,
        by decide, by decide, by decide⟩
    · exact ZReplay.pair (by decide)

private theorem znonzero : ∀ q ∈ [zf, zs₁, zs₂, zs₃], q ≠ 0 := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> decide

private theorem zderiv :
    Hex.DensePoly.derivative zf = Hex.DensePoly.scale 1 zs₁ := by
  decide

private def zinterval₁ : Hex.DyadicInterval :=
  Hex.DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt (-1)) (by decide)

private def zinterval₂ : Hex.DyadicInterval :=
  Hex.DyadicInterval.mk (Dyadic.ofInt (-1)) (Dyadic.ofInt 0) (by decide)

private def zinterval₃ : Hex.DyadicInterval :=
  Hex.DyadicInterval.mk (Dyadic.ofInt 0) (Dyadic.ofInt 2) (by decide)

private def zcount (I : Hex.DyadicInterval) : Int :=
  (Hex.sturmVarAt [zf, zs₁, zs₂, zs₃].toArray I.lower : Int) -
    Hex.sturmVarAt [zf, zs₁, zs₂, zs₃].toArray I.upper

private def ztotal : Int :=
  (Hex.sturmVarNegInf [zf, zs₁, zs₂, zs₃].toArray : Int) -
    Hex.sturmVarPosInf [zf, zs₁, zs₂, zs₃].toArray

private def zisolations : LiteralIsolations zcount ztotal where
  isolations := #[⟨zinterval₁, by decide⟩, ⟨zinterval₂, by decide⟩,
    ⟨zinterval₃, by decide⟩]
  ordered := by decide
  complete := by decide

private theorem zcount_exact (i : Fin zisolations.isolations.size) :
    zcount zisolations.isolations[i].interval =
      (Literal.rootsIn (toPolyℝ zf) zisolations.isolations[i].interval).card := by
  simpa only [zcount] using
    zreplay.count_eq_card_roots znonzero 1 (by decide) zderiv
      zisolations.isolations[i].interval

private theorem ztotal_exact :
    ztotal = ((toPolyℝ zf).roots.card : Int) := by
  simpa only [ztotal] using
    zreplay.total_eq_card_roots znonzero 1 (by decide) zderiv

example : ∀ r : ℝ, (toPolyℝ zf).IsRoot r →
    ∃! i : Fin zisolations.isolations.size,
      Literal.InInterval zisolations.isolations[i].interval r := by
  apply LiteralIsolations.isolates (p := zf) (by decide)
    (zreplay.squarefree 1 (by decide) zderiv) zisolations
    zcount_exact ztotal_exact

end HexRealRootsMathlib.LiteralChainTests
