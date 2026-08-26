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

private theorem insertVar_mul (i : Fin (n + 1)) (ea eb : Nat)
    (a b : Mono n) :
    insertVar i (ea + eb) (Mono.mul a b) =
      Mono.mul (insertVar i ea a) (insertVar i eb b) := by
  apply Vector.ext
  intro j hj
  by_cases heq : j = i.val
  · simp [insertVar, Mono.mul, heq]
  · by_cases hlt : j < i.val <;>
      simp [insertVar, Mono.mul, heq, hlt]

private theorem insertVar_mul_zero (i : Fin (n + 1)) (a b : Mono n) :
    insertVar i 0 (Mono.mul a b) =
      Mono.mul (insertVar i 0 a) (insertVar i 0 b) := by
  simpa using insertVar_mul i 0 0 a b

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

/-- The full coefficient of a constant embedding is supported exactly on
monomials having selected-variable degree zero. -/
theorem coeff_constIn_term (i : Fin (n + 1))
    (c : MvPoly n R cmp') (m : Mono (n + 1)) :
    coeff m (constIn (cmp := cmp) i cmp' c) =
      if Mono.degreeOf i m = 0 then coeff (removeVar i m) c else 0 := by
  by_cases hdegree : Mono.degreeOf i m = 0
  · rw [Hex.ite_eq_left hdegree]
    calc
      coeff m (constIn (cmp := cmp) i cmp' c) =
          coeff (insertVar i (Mono.degreeOf i m) (removeVar i m))
            (constIn (cmp := cmp) i cmp' c) := by
        rw [insertVar_removeVar]
      _ = coeff (removeVar i m) c := by
        unfold constIn
        rw [ofUnivariate_coeff, DensePoly.coeff_C, hdegree,
          Hex.ite_eq_left rfl]
  · rw [Hex.ite_eq_right hdegree]
    calc
      coeff m (constIn (cmp := cmp) i cmp' c) =
          coeff (insertVar i (Mono.degreeOf i m) (removeVar i m))
            (constIn (cmp := cmp) i cmp' c) := by
        rw [insertVar_removeVar]
      _ = 0 := by
        unfold constIn
        rw [ofUnivariate_coeff, DensePoly.coeff_C,
          Hex.ite_eq_right hdegree]
        change coeff (removeVar i m) (0 : MvPoly n R cmp') = 0
        rw [coeff_zero]

private theorem splits_const_perm (i : Fin (n + 1)) (e : Nat)
    (m : Mono n) :
    ((Mono.splits m).map fun ab =>
      (insertVar i 0 ab.1, insertVar i e ab.2)).Perm
        ((Mono.splits (insertVar i e m)).filter fun ab =>
          decide (Mono.degreeOf i ab.1 = 0)) := by
  let lift : Mono n × Mono n → Mono (n + 1) × Mono (n + 1) :=
    fun ab => (insertVar i 0 ab.1, insertVar i e ab.2)
  have hinj : Function.Injective lift := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    apply Prod.ext
    · exact ((insertVar_inj i 0 0 a c).mp (congrArg Prod.fst h)).2
    · exact ((insertVar_inj i e e b d).mp (congrArg Prod.snd h)).2
  have hleft : ((Mono.splits m).map lift).Nodup := by
    apply (Mono.splits_nodup m).map
    intro a b hne heq
    exact hne (hinj heq)
  have hright :
      ((Mono.splits (insertVar i e m)).filter fun ab =>
        decide (Mono.degreeOf i ab.1 = 0)).Nodup :=
    (Mono.splits_nodup (insertVar i e m)).filter _
  apply (List.perm_ext_iff_of_nodup hleft hright).mpr
  rintro ⟨a, b⟩
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨c, d⟩, hcd, hab⟩
    cases hab
    rw [List.mem_filter]
    constructor
    · apply (Mono.splits_mem_iff ..).mpr
      rw [← insertVar_mul i 0 e, (Mono.splits_mem_iff ..).mp hcd]
      simp
    · simp
  · intro hmem
    rw [List.mem_filter] at hmem
    have hmul : Mono.mul a b = insertVar i e m :=
      (Mono.splits_mem_iff ..).mp hmem.1
    have ha0 : Mono.degreeOf i a = 0 := by simpa using hmem.2
    have hsum := congrArg (Mono.degreeOf i) hmul
    rw [degreeOf_mul, degreeOf_insertVar, ha0, Nat.zero_add] at hsum
    have ha : insertVar i 0 (removeVar i a) = a := by
      rw [← ha0]
      exact insertVar_removeVar i a
    have hb : insertVar i e (removeVar i b) = b := by
      rw [← hsum]
      exact insertVar_removeVar i b
    apply List.mem_map.mpr
    refine ⟨(removeVar i a, removeVar i b), ?_, Prod.ext ha hb⟩
    apply (Mono.splits_mem_iff ..).mpr
    rw [← removeVar_mul, hmul, removeVar_insertVar]

/-- Multiplication by a constant embedding acts coefficientwise in the
selected-variable recursive view. -/
theorem coeff_constIn_mul (i : Fin (n + 1))
    (c : MvPoly n R cmp') (p : MvPoly (n + 1) R cmp) (e : Nat) :
    (toUnivariate i cmp' (constIn i cmp' c * p)).coeff e =
      c * (toUnivariate i cmp' p).coeff e := by
  apply MvPoly.ext
  intro m
  rw [toUnivariate_coeff, coeff_mul, coeff_mul]
  let fullTerm : Mono (n + 1) × Mono (n + 1) → R := fun ab =>
    coeff ab.1 (constIn (cmp := cmp) i cmp' c) * coeff ab.2 p
  let lowerTerm : Mono n × Mono n → R := fun ab =>
    coeff ab.1 c * coeff ab.2 ((toUnivariate i cmp' p).coeff e)
  calc
    (Mono.splits (insertVar i e m)).foldl
        (fun acc ab => acc + fullTerm ab) 0 =
        ((Mono.splits (insertVar i e m)).filter fun ab =>
          decide (Mono.degreeOf i ab.1 = 0)).foldl
            (fun acc ab => acc + fullTerm ab) 0 := by
      symm
      rw [List.foldl_filter]
      apply List.foldl_congr
      intro acc ab _
      by_cases hdegree : Mono.degreeOf i ab.1 = 0
      · simp [hdegree]
      · unfold fullTerm
        rw [coeff_constIn_term, Hex.ite_eq_right hdegree]
        rw [Lean.Grind.Semiring.zero_mul,
          Lean.Grind.AddCommMonoid.add_zero]
        simp [hdegree]
    _ = ((Mono.splits m).map fun ab =>
          (insertVar i 0 ab.1, insertVar i e ab.2)).foldl
            (fun acc ab => acc + fullTerm ab) 0 :=
      List.foldl_add_perm fullTerm (splits_const_perm i e m).symm 0
    _ = (Mono.splits m).foldl
          (fun acc ab => acc + lowerTerm ab) 0 := by
      rw [List.foldl_map]
      apply List.foldl_congr
      intro acc ab _
      unfold fullTerm lowerTerm
      rw [coeff_constIn_term, degreeOf_insertVar, Hex.ite_eq_left rfl,
        removeVar_insertVar,
        ← toUnivariate_coeff (cmp' := cmp') i p e ab.2]

/-- A polynomial in the remaining variables divides a polynomial in the full
ring when it divides every coefficient of the selected-variable view. -/
theorem constIn_dvd (i : Fin (n + 1)) (d : MvPoly n R cmp')
    (p : MvPoly (n + 1) R cmp)
    (h : ∀ k, d ∣ (toUnivariate i cmp' p).coeff k) :
    constIn (cmp := cmp) i cmp' d ∣ p := by
  classical
  let view := toUnivariate i cmp' p
  let qs : Nat → MvPoly n R cmp' := fun k => Classical.choose (h k)
  have hqs (k : Nat) : view.coeff k = qs k * d := by
    exact Classical.choose_spec (h k)
  let qView : DensePoly (MvPoly n R cmp') :=
    DensePoly.ofCoeffs (Array.ofFn (n := view.size) fun k => qs k)
  let q := ofUnivariate (cmp := cmp) i cmp' qView
  have hqView : toUnivariate i cmp' q = qView := by
    unfold q
    exact toUnivariate_ofUnivariate i qView
  refine ⟨q, ?_⟩
  apply MvPoly.ext
  intro m
  rw [← insertVar_removeVar i m]
  rw [← toUnivariate_coeff (cmp' := cmp') i p,
    ← toUnivariate_coeff (cmp' := cmp') i (q * constIn i cmp' d)]
  rw [MvPoly.mul_comm q (constIn i cmp' d), coeff_constIn_mul]
  rw [hqView]
  apply congrArg (coeff (removeVar i m))
  change view.coeff (Mono.degreeOf i m) = d * qView.coeff (Mono.degreeOf i m)
  let e := Mono.degreeOf i m
  change view.coeff e = d * qView.coeff e
  unfold qView
  rw [DensePoly.coeff_ofCoeffs]
  by_cases he : e < view.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      Hex.dite_eq_left he]
    simp only [Option.getD_some]
    rw [hqs]
    exact Lean.Grind.CommSemiring.mul_comm _ _
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
      Hex.dite_eq_right he]
    simp only [Option.getD_none]
    rw [DensePoly.coeff_eq_zero_of_size_le view (Nat.le_of_not_gt he)]
    change (0 : MvPoly n R cmp') = d * 0
    exact (MvPoly.mul_zero d).symm

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
