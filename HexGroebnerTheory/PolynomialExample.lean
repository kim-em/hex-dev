/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGroebnerTheory.GeneratedExample
public import Mathlib.Tactic.FinCases

public section

namespace HexGroebnerTheory.PolynomialExample
open MvPolynomial
open scoped HexMvPolyTheory HexModArithTheory.ZMod64

local instance : Hex.ZMod64.Bounds 7 := ⟨by decide, by decide⟩


private theorem exponents (a b : Nat) :
    HexMvPolyTheory.monoEquiv (Hex.MvPoly.Kernel.mono 2 [a, b]) =
      Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b := by
  ext i
  fin_cases i <;> simp [Hex.MvPoly.Kernel.mono, HexMvPolyTheory.monoEquiv_apply]

private theorem expansion (a b : Nat) (c : ZMod 7) :
    (monomial (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b) (c : ZMod 7) :
      MvPolynomial (Fin 2) (ZMod 7)) = C (c : ZMod 7) * X 0^a * X 1^b := by
  rw [monomial_add_single, ← C_mul_X_pow_eq_monomial]

private theorem term (a b c : Nat) :
    @Eq (MvPolynomial (Fin 2) (ZMod 7))
      (denote GeneratedExample.context [([a, b],c)])
      (C (c : ZMod 7) * X (0 : Fin 2)^a * X 1^b) := by
  change HexMvPolyTheory.Kernel.denoteMod 7
    (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2) [([a, b],c)] =
    (C (c : ZMod 7) * X (0 : Fin 2)^a * X 1^b : MvPolynomial (Fin 2) (ZMod 7))
  simp only [HexMvPolyTheory.Kernel.denoteMod_cons,HexMvPolyTheory.Kernel.denoteMod_nil,add_zero,exponents]
  exact expansion a b c

private theorem firstIdentity :
    (monomial (Finsupp.single (0 : Fin 2) 2 + Finsupp.single 1 0) (1 : ZMod 7) +
      monomial (Finsupp.single 0 0 + Finsupp.single 1 1) 6 :
      MvPolynomial (Fin 2) (ZMod 7)) = X 0^2-X 1 := by
  rw [expansion 2 0 1,expansion 0 1 6]
  rw [show (6 : ZMod 7) = -1 from by decide +kernel]
  simp [sub_eq_add_neg]

private theorem secondIdentity :
    (monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) (1 : ZMod 7) +
      monomial (Finsupp.single 0 0 + Finsupp.single 1 0) 6 :
      MvPolynomial (Fin 2) (ZMod 7)) = X 0*X 1-1 := by
  rw [expansion 1 1 1,expansion 0 0 6]
  rw [show (6 : ZMod 7) = -1 from by decide +kernel]
  simp [sub_eq_add_neg]

private theorem input0 :
    @Eq (MvPolynomial (Fin 2) (ZMod 7))
      (denote GeneratedExample.context [([2,0],1),([0,1],6)])
      (X (0 : Fin 2)^2-X 1) := by
  change HexMvPolyTheory.Kernel.denoteMod 7
    (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2) [([2,0],1),([0,1],6)] = _
  simp only [HexMvPolyTheory.Kernel.denoteMod_cons,
    HexMvPolyTheory.Kernel.denoteMod_nil,add_zero,exponents]
  exact firstIdentity

private theorem input1 :
    @Eq (MvPolynomial (Fin 2) (ZMod 7))
      (denote GeneratedExample.context [([1,1],1),([0,0],6)])
      (X (0 : Fin 2)*X 1-1) := by
  change HexMvPolyTheory.Kernel.denoteMod 7
    (cmp := Hex.Groebner.TermOrder.grevlex.cmp 2) [([1,1],1),([0,0],6)] = _
  simp only [HexMvPolyTheory.Kernel.denoteMod_cons,
    HexMvPolyTheory.Kernel.denoteMod_nil,add_zero,exponents]
  exact secondIdentity

private theorem generators : (Set.range fun i : Fin GeneratedExample.generators.size =>
    (denote GeneratedExample.context GeneratedExample.generators[i] : MvPolynomial (Fin 2) (ZMod 7))) =
      {X (0 : Fin 2)^2-X 1,X (0 : Fin 2)*X 1-1} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i
    · exact Or.inl input0
    · exact Or.inr input1
  · intro hf
    rcases Set.mem_insert_iff.mp hf with hf | hf
    · exact ⟨⟨0,by decide +kernel⟩,input0.trans hf.symm⟩
    · have hf := Set.mem_singleton_iff.mp hf
      exact ⟨⟨1,by decide +kernel⟩,input1.trans hf.symm⟩

/-- A Mathlib ideal statement proved by replaying the generated complete basis. -/
theorem x_not_mem : X (0 : Fin 2) ∉ Ideal.span
    ({X (0 : Fin 2)^2-X 1,X (0 : Fin 2)*X 1-1} : Set (MvPolynomial (Fin 2) (ZMod 7))) := by
  have checked := GeneratedExample.x_not_mem
  have target : (denote GeneratedExample.context GeneratedExample.target :
      MvPolynomial (Fin 2) (ZMod 7)) = X (0 : Fin 2) := by
    have h := term 1 0 1
    change denote GeneratedExample.context [([1,0],1)] =
      (C (1 : ZMod 7) * X (0 : Fin 2)^1 * X 1^0 : MvPolynomial (Fin 2) (ZMod 7)) at h
    simpa only [GeneratedExample.target,Hex.Groebner.PrimeExample.target,map_one,pow_one,pow_zero,one_mul,mul_one] using h
  rw [target,generators] at checked
  exact checked

/-- info: 'HexGroebnerTheory.PolynomialExample.x_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x_not_mem

end HexGroebnerTheory.PolynomialExample
