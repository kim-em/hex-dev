/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Union
public import HexRealRootsMathlib.RealClosed

public section

noncomputable section
namespace Hex.RealClosure.Union.Tests

attribute [local instance 2000] Field.toGrindField
open Polynomial

/-- The usual rational embedding in the real numbers satisfies the union theorem. -/
example : IsRealClosed (Carrier Rat ℝ) := realClosed

/-- The restriction constructor applies to the actual nonalgebraic real ambient. -/
example : Ambient Rat := Ambient.ofUnion ℝ Rat.cast_strictMono

private theorem sqrt_member (n : Nat) : Real.sqrt n ∈ field Rat ℝ := by
  apply root_mem (X ^ 2 - C (n : Carrier Rat ℝ))
    (X_pow_sub_C_ne_zero (by decide) _) (Real.sqrt n)
  simp only [IsRoot.def, eval_map, eval₂_sub, eval₂_pow, eval₂_X, eval₂_natCast,
    map_natCast]
  rw [Real.sq_sqrt (by positivity), sub_self]

/-- One finite compatible extension contains both actual selected real square roots. -/
example : ∃ common : IntermediateField Rat ℝ,
    FiniteDimensional Rat common ∧ common ≤ field Rat ℝ ∧
      Real.sqrt 2 ∈ common ∧ Real.sqrt 3 ∈ common := by
  classical
  have two : ∀ x ∈ ({Real.sqrt 2} : Finset ℝ), IsAlgebraic Rat x := by
    simpa using (mem_iff _).mp (sqrt_member 2)
  have three : ∀ x ∈ ({Real.sqrt 3} : Finset ℝ), IsAlgebraic Rat x := by
    simpa using (mem_iff _).mp (sqrt_member 3)
  obtain ⟨common, dimension, member, left, right⟩ := common_extension _ _ two three
  refine ⟨common, dimension, member, left ?_, right ?_⟩
  · exact mem_adjoin _ _ (Finset.mem_singleton_self _)
  · exact mem_adjoin _ _ (Finset.mem_singleton_self _)

/-- Every element of the actual Tau Ceti ambient lies in its algebraic union. -/
example :
    let ambient := Ambient.ofField Rat
    let _ : Algebra Rat ambient.Carrier := ambient.inclusion.toAlgebra
    field Rat ambient.Carrier = ⊤ := Ambient.union_eq_top _

open scoped Hex.OrderedFn.Infinitesimal

private abbrev Base := @Hex.RationalFn Rat (Field.toGrindField (K := Rat)) inferInstance
private noncomputable def ambient : Ambient Base := Ambient.infinitesimal Rat

/-- A nonrational base retains its actual chosen inclusion through restriction. -/
example (a : Base) :
    let _ : Algebra Base ambient.Carrier := ambient.inclusion.toAlgebra
    inclusion ((Ambient.ofUnion ambient.Carrier ambient.monotone).inclusion a) =
      ambient.inclusion a := by
  let _ : Algebra Base ambient.Carrier := ambient.inclusion.toAlgebra
  exact Ambient.ofUnion_inclusion _ _ a

private noncomputable def wide : Ambient (Hex.RationalFn Base) := Ambient.infinitesimal Base

private noncomputable def embedding : Base →+* wide.Carrier :=
  wide.inclusion.comp HexRationalFnMathlib.constantHom

private theorem embedding_monotone : StrictMono embedding := by
  intro a b less
  exact wide.monotone ((Hex.OrderedFn.Infinitesimal.C_lt a b).mpr less)

/-- Restrict a second infinitesimal ambient over the first rational-function
base, then carry its square root of the first infinitesimal back into that ambient. -/
example :
    let _ : Algebra Base wide.Carrier := embedding.toAlgebra
    ∃ s : (Ambient.ofUnion wide.Carrier embedding_monotone).Carrier,
      0 < s ∧
      (Ambient.ofUnion.val wide.Carrier embedding_monotone s) ^ 2 =
        embedding (Hex.RationalFn.X : Base) := by
  let _ : Algebra Base wide.Carrier := embedding.toAlgebra
  let restricted := Ambient.ofUnion wide.Carrier embedding_monotone
  obtain ⟨s, positive, square, _, _⟩ := restricted.exists_sqrt
    (Hex.RationalFn.X : Base) Hex.OrderedFn.Infinitesimal.X_pos
    (by simpa only [Hex.RationalFn.C_one] using
      Hex.OrderedFn.Infinitesimal.X_lt_C (1 : Rat) zero_lt_one)
  refine ⟨s, positive, ?_⟩
  rw [← map_pow, square, Ambient.ofUnion.val_inclusion]
  rfl

end Hex.RealClosure.Union.Tests
