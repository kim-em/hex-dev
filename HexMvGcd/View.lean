/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
public import HexMvGcd.Divide
public import HexMvPoly.Recursive

@[expose] public section
set_option backward.proofsInPublic true

/-!
The constant embedding associated to the arity-dropping univariate view.

Keeping this operation next to the gcd code avoids adding a second recursive
view to `hex-mv-poly`: being constant in the selected variable is represented
by applying `ofUnivariate` to a dense constant polynomial.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  {cmp' : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]

/-- Embed a polynomial in the remaining variables as a polynomial constant in
the selected variable. -/
def constIn (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (c : MvPoly n R cmp') : MvPoly (n + 1) R cmp :=
  ofUnivariate (cmp := cmp) i cmp' (DensePoly.C c)

omit [BEq R] [LawfulBEq R] in
/-- The recursive view of a constant embedding is a dense constant. -/
@[simp] theorem toUnivariate_constIn (i : Fin (n + 1))
    (c : MvPoly n R cmp') :
    toUnivariate i cmp' (constIn (cmp := cmp) i cmp' c) = DensePoly.C c := by
  exact toUnivariate_ofUnivariate i (DensePoly.C c)

/-- The degree-`k` recursive coefficient of `constIn c` is `c` at zero and
zero elsewhere. -/
@[simp] theorem coeff_constIn (i : Fin (n + 1))
    (c : MvPoly n R cmp') (k : Nat) :
    (toUnivariate i cmp' (constIn (cmp := cmp) i cmp' c)).coeff k =
      if k = 0 then c else 0 := by
  rw [toUnivariate_constIn]
  exact DensePoly.coeff_C c k

/-- Constant embedding preserves zero. -/
@[simp] theorem constIn_zero (i : Fin (n + 1)) :
    constIn (R := R) (cmp := cmp) i cmp' 0 = 0 := by
  apply MvPoly.ext
  intro m
  unfold constIn
  rw [← insertVar_removeVar i m, ofUnivariate_coeff, DensePoly.coeff_C,
    insertVar_removeVar]
  split <;> rw [coeff_zero] <;> rfl

/-- Constant embedding preserves one. -/
@[simp] theorem constIn_one (i : Fin (n + 1)) :
    constIn (R := R) (cmp := cmp) i cmp' 1 = 1 := by
  apply MvPoly.ext
  intro m
  unfold constIn
  rw [← insertVar_removeVar i m, ofUnivariate_coeff, DensePoly.coeff_C,
    insertVar_removeVar]
  by_cases hdegree : Mono.degreeOf i m = 0
  · rw [Hex.ite_eq_left hdegree, coeff_one]
    have hzero : insertVar i 0 (Mono.zero : Mono n) = Mono.zero := by
      apply Vector.ext
      intro j hj
      simp [insertVar, Mono.zero]
    have hm : m = Mono.zero ↔ removeVar i m = Mono.zero := by
      constructor
      · intro h
        subst m
        simp [removeVar, Mono.zero]
      · intro h
        calc
          m = insertVar i (Mono.degreeOf i m) (removeVar i m) :=
            (insertVar_removeVar i m).symm
          _ = insertVar i 0 Mono.zero := by rw [hdegree, h]
          _ = Mono.zero := hzero
    rw [coeff_one]
    simp only [hm]
  · rw [Hex.ite_eq_right hdegree]
    have hm : m ≠ Mono.zero := by
      intro h
      subst m
      exact hdegree (by
        unfold Mono.degreeOf
        exact Mono.getElem_zero i)
    change coeff (removeVar i m) (0 : MvPoly n R cmp') = coeff m 1
    rw [coeff_zero, coeff_one, Hex.ite_eq_right hm]

/-- Constant embedding preserves addition. -/
theorem constIn_add (i : Fin (n + 1)) (a b : MvPoly n R cmp') :
    constIn (cmp := cmp) i cmp' (a + b) =
      constIn i cmp' a + constIn i cmp' b := by
  apply MvPoly.ext
  intro m
  unfold constIn
  rw [← insertVar_removeVar i m, ofUnivariate_coeff, coeff_add,
    ofUnivariate_coeff, ofUnivariate_coeff, DensePoly.coeff_C,
    DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hdegree : Mono.degreeOf i m = 0
  · simp only [hdegree, Hex.ite_eq_left, coeff_add]
  · simp only [hdegree]
    change coeff (removeVar i m) (0 : MvPoly n R cmp') =
      coeff (removeVar i m) (0 : MvPoly n R cmp') +
        coeff (removeVar i m) (0 : MvPoly n R cmp')
    rw [coeff_zero, Lean.Grind.AddCommMonoid.zero_add]

private theorem degreeOf_mul (i : Fin (n + 1))
    (a b : Mono (n + 1)) :
    Mono.degreeOf i (Mono.mul a b) =
      Mono.degreeOf i a + Mono.degreeOf i b := by
  unfold Mono.degreeOf
  exact Mono.getElem_mul a b i

private theorem insertVar_mul_zero (i : Fin (n + 1)) (a b : Mono n) :
    insertVar i 0 (Mono.mul a b) =
      Mono.mul (insertVar i 0 a) (insertVar i 0 b) := by
  apply Vector.ext
  intro j hj
  by_cases heq : j = i.val
  · simp [insertVar, Mono.mul, heq]
  · by_cases hlt : j < i.val <;>
      simp [insertVar, Mono.mul, heq, hlt]

private theorem removeVar_mul (i : Fin (n + 1)) (a b : Mono (n + 1)) :
    removeVar i (Mono.mul a b) =
      Mono.mul (removeVar i a) (removeVar i b) := by
  apply Vector.ext
  intro j hj
  by_cases hlt : j < i.val <;> simp [removeVar, Mono.mul, hlt]

private theorem splits_insertVar_zero_perm (i : Fin (n + 1)) (m : Mono n) :
    ((Mono.splits m).map fun ab =>
      (insertVar i 0 ab.1, insertVar i 0 ab.2)).Perm
        (Mono.splits (insertVar i 0 m)) := by
  let lift : Mono n × Mono n → Mono (n + 1) × Mono (n + 1) :=
    fun ab => (insertVar i 0 ab.1, insertVar i 0 ab.2)
  have hinj : Function.Injective lift := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    apply Prod.ext
    · exact ((insertVar_inj i 0 0 a c).mp (congrArg Prod.fst h)).2
    · exact ((insertVar_inj i 0 0 b d).mp (congrArg Prod.snd h)).2
  have hnodup : ((Mono.splits m).map lift).Nodup := by
    apply (Mono.splits_nodup m).map
    intro a b hne heq
    exact hne (hinj heq)
  apply (List.perm_ext_iff_of_nodup hnodup
    (Mono.splits_nodup (insertVar i 0 m))).mpr
  rintro ⟨a, b⟩
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨c, d⟩, hcd, hab⟩
    cases hab
    apply (Mono.splits_mem_iff ..).mpr
    rw [← insertVar_mul_zero, (Mono.splits_mem_iff ..).mp hcd]
  · intro hmem
    have hmul : Mono.mul a b = insertVar i 0 m :=
      (Mono.splits_mem_iff ..).mp hmem
    have hdegree : Mono.degreeOf i a + Mono.degreeOf i b = 0 := by
      calc
        Mono.degreeOf i a + Mono.degreeOf i b =
            Mono.degreeOf i (Mono.mul a b) := (degreeOf_mul i a b).symm
        _ = Mono.degreeOf i (insertVar i 0 m) := by rw [hmul]
        _ = 0 := degreeOf_insertVar i 0 m
    have ha0 : Mono.degreeOf i a = 0 := by omega
    have hb0 : Mono.degreeOf i b = 0 := by omega
    have ha : insertVar i 0 (removeVar i a) = a := by
      rw [← ha0]
      exact insertVar_removeVar i a
    have hb : insertVar i 0 (removeVar i b) = b := by
      rw [← hb0]
      exact insertVar_removeVar i b
    apply List.mem_map.mpr
    refine ⟨(removeVar i a, removeVar i b), ?_, ?_⟩
    · apply (Mono.splits_mem_iff ..).mpr
      rw [← removeVar_mul, hmul, removeVar_insertVar]
    · exact Prod.ext ha hb

/-- Constant embedding preserves multiplication. -/
theorem constIn_mul (i : Fin (n + 1)) (a b : MvPoly n R cmp') :
    constIn (cmp := cmp) i cmp' (a * b) =
      constIn i cmp' a * constIn i cmp' b := by
  apply MvPoly.ext
  intro m
  unfold constIn
  rw [← insertVar_removeVar i m, ofUnivariate_coeff, coeff_mul]
  simp only [DensePoly.coeff_C]
  split
  · rename_i hdegree
    simp only [hdegree, coeff_mul]
    let term : Mono (n + 1) × Mono (n + 1) → R := fun ab =>
      coeff ab.1 (ofUnivariate (cmp := cmp) i cmp' (DensePoly.C a)) *
        coeff ab.2 (ofUnivariate (cmp := cmp) i cmp' (DensePoly.C b))
    calc
      (Mono.splits (removeVar i m)).foldl
          (fun acc ab => acc + coeff ab.1 a * coeff ab.2 b) 0 =
          ((Mono.splits (removeVar i m)).map fun ab =>
            (insertVar i 0 ab.1, insertVar i 0 ab.2)).foldl
              (fun acc ab => acc + term ab) 0 := by
            rw [List.foldl_map]
            apply List.foldl_congr
            intro acc ab hab
            unfold term
            rw [ofUnivariate_coeff, ofUnivariate_coeff,
              DensePoly.coeff_C, DensePoly.coeff_C]
            simp
      _ = (Mono.splits (insertVar i 0 (removeVar i m))).foldl
          (fun acc ab => acc + term ab) 0 :=
        List.foldl_add_perm term
          (splits_insertVar_zero_perm i (removeVar i m)) 0
  · rename_i hdegree
    change coeff (removeVar i m) (0 : MvPoly n R cmp') = _
    rw [coeff_zero]
    symm
    apply List.foldl_add_eq_self
    intro ab hab
    have hmul : Mono.mul ab.1 ab.2 =
        insertVar i (Mono.degreeOf i m) (removeVar i m) :=
      (Mono.splits_mem_iff ..).mp hab
    have hsum : Mono.degreeOf i ab.1 + Mono.degreeOf i ab.2 =
        Mono.degreeOf i m := by
      calc
        Mono.degreeOf i ab.1 + Mono.degreeOf i ab.2 =
            Mono.degreeOf i (Mono.mul ab.1 ab.2) :=
          (degreeOf_mul i ab.1 ab.2).symm
        _ = Mono.degreeOf i
            (insertVar i (Mono.degreeOf i m) (removeVar i m)) := by rw [hmul]
        _ = Mono.degreeOf i m := degreeOf_insertVar ..
    have hnonzero : Mono.degreeOf i ab.1 ≠ 0 ∨
        Mono.degreeOf i ab.2 ≠ 0 := by
      by_cases hleft : Mono.degreeOf i ab.1 ≠ 0
      · exact Or.inl hleft
      · apply Or.inr
        intro hright
        apply hdegree
        omega
    rcases hnonzero with hleft | hright
    · have hz : coeff ab.1
          (ofUnivariate (cmp := cmp) i cmp' (DensePoly.C a)) = 0 := by
        rw [← insertVar_removeVar i ab.1, ofUnivariate_coeff,
          DensePoly.coeff_C, Hex.ite_eq_right hleft]
        exact coeff_zero _
      rw [hz, Lean.Grind.Semiring.zero_mul]
    · have hz : coeff ab.2
          (ofUnivariate (cmp := cmp) i cmp' (DensePoly.C b)) = 0 := by
        rw [← insertVar_removeVar i ab.2, ofUnivariate_coeff,
          DensePoly.coeff_C, Hex.ite_eq_right hright]
        exact coeff_zero _
      rw [hz, Lean.Grind.Semiring.mul_zero]

omit [BEq R] [LawfulBEq R] in
/-- Constant embedding is injective. -/
theorem constIn_injective (i : Fin (n + 1)) :
    Function.Injective (constIn (R := R) (cmp := cmp) i cmp') := by
  intro a b h
  have hview := congrArg (toUnivariate i cmp') h
  rw [toUnivariate_constIn, toUnivariate_constIn] at hview
  have hcoeff := congrArg (fun p : DensePoly (MvPoly n R cmp') => p.coeff 0) hview
  simpa using hcoeff

/-- The degree in the selected variable, with `none` distinguishing zero from
a constant polynomial. -/
def degreeIn? (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (p : MvPoly (n + 1) R cmp) : Option Nat :=
  (toUnivariate i cmp' p).degree?

/-- Coefficient slice at a named degree in the selected variable. -/
def coeffIn (i : Fin (n + 1)) (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (k : Nat) (p : MvPoly (n + 1) R cmp) : MvPoly n R cmp' :=
  (toUnivariate i cmp' p).coeff k

end Hex.MvPoly
