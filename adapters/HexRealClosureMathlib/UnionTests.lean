/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Union
public import TauCeti.FieldTheory.IsRealClosed.Real

public section

noncomputable section
namespace Hex.RealClosure.Union.Tests
open Polynomial

/-- The usual rational embedding in the real numbers satisfies the union theorem. -/
example : IsRealClosed (Carrier Rat ℝ) := realClosed

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

end Hex.RealClosure.Union.Tests
