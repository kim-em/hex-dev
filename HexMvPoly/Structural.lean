/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Eval

@[expose] public section

/-!
Structural transformations of `Hex.MvPoly`: reordering, renaming,
differentiation, homogeneous restriction, and substitution.
-/

namespace Hex.MvPoly

universe u v

variable {n k : Nat} {R : Type u} {S : Type v}
  {cmp : Mono n → Mono n → Ordering}
  {targetCmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Std.TransCmp targetCmp] [Std.LawfulEqCmp targetCmp]

/-- Rebuild a polynomial under a different monomial comparator. -/
def reorder (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : MvPoly n R cmp' :=
  ofTerms p.termsList

/-- Rename variables, adding exponents in fibres and combining all resulting
term collisions. -/
def rename (cmp' : Mono k → Mono k → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → Fin k) (p : MvPoly n R cmp) : MvPoly k R cmp' :=
  p.foldTerms
    (fun acc m c => acc.addMonomial (Mono.rename f m) c)
    0

/-- Decrease the exponent at `i` by one, leaving every other exponent
unchanged. -/
def predAt (i : Fin n) (m : Mono n) : Mono n :=
  Hex.Vector.ofFn' fun j => if j = i then m[j] - 1 else m[j]

@[simp] theorem degreeOf_succAt (i : Fin n) (m : Mono n) :
    Mono.degreeOf i (Mono.succAt i m) = Mono.degreeOf i m + 1 := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have get_mul (a b : Mono n) (j : Fin n) :
      (Mono.mul a b).get j = a.get j + b.get j := by
    unfold Mono.mul
    rw [get_ofFn]
    rfl
  have get_unit (j : Fin n) :
      (Mono.unit i).get j = if j = i then 1 else 0 := by
    unfold Mono.unit
    rw [get_ofFn]
  unfold Mono.degreeOf Mono.succAt
  change (Mono.mul m (Mono.unit i)).get i = m.get i + 1
  rw [get_mul, get_unit]
  simp

@[simp] theorem predAt_succAt (i : Fin n) (m : Mono n) :
    predAt i (Mono.succAt i m) = m := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have get_mul (a b : Mono n) (j : Fin n) :
      (Mono.mul a b).get j = a.get j + b.get j := by
    unfold Mono.mul
    rw [get_ofFn]
    rfl
  have get_unit (j : Fin n) :
      (Mono.unit i).get j = if j = i then 1 else 0 := by
    unfold Mono.unit
    rw [get_ofFn]
  apply Vector.ext
  intro j hj
  let k : Fin n := ⟨j, hj⟩
  change (predAt i (Mono.succAt i m)).get k = m.get k
  unfold predAt Mono.succAt
  rw [get_ofFn]
  change
    (if k = i then
      (Mono.mul m (Mono.unit i)).get k - 1
    else (Mono.mul m (Mono.unit i)).get k) = m.get k
  rw [get_mul, get_unit]
  by_cases hki : k = i
  · simp [hki]
  · simp [hki]

theorem predAt_eq_iff (i : Fin n) (m t : Mono n)
    (ht : Mono.degreeOf i t ≠ 0) :
    predAt i t = m ↔ t = Mono.succAt i m := by
  have get_ofFn {r : Nat} (g : Fin r → Nat) (j : Fin r) :
      (Hex.Vector.ofFn' g).get j = g j := by
    change (Hex.Vector.ofFn' g)[j.val] = g j
    rw [Hex.Vector.getElem_ofFn' g j.val j.isLt]
  have get_mul (a b : Mono n) (j : Fin n) :
      (Mono.mul a b).get j = a.get j + b.get j := by
    unfold Mono.mul
    rw [get_ofFn]
    rfl
  have get_unit (j : Fin n) :
      (Mono.unit i).get j = if j = i then 1 else 0 := by
    unfold Mono.unit
    rw [get_ofFn]
  constructor
  · intro h
    apply Vector.ext
    intro j hj
    let k : Fin n := ⟨j, hj⟩
    have hk := congrArg (fun a : Mono n => a.get k) h
    change (predAt i t).get k = m.get k at hk
    unfold predAt at hk
    rw [get_ofFn] at hk
    change (if k = i then t.get k - 1 else t.get k) = m.get k at hk
    change t.get k = (Mono.succAt i m).get k
    unfold Mono.succAt
    change t.get k = (Mono.mul m (Mono.unit i)).get k
    rw [get_mul, get_unit]
    by_cases hki : k = i
    · rw [hki] at hk ⊢
      simp only [if_pos] at hk ⊢
      have ht' : t.get i ≠ 0 := by
        exact ht
      omega
    · simp only [if_neg hki]
      simp only [if_neg hki] at hk
      exact hk
  · rintro rfl
    exact predAt_succAt i m

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Formal derivative with respect to variable `i`. -/
def derivative [Zero R] [NatCast R] [Add R] [Mul R] [DecidableEq R]
    (i : Fin n) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc m c =>
      let e := Mono.degreeOf i m
      if e = 0 then acc
      else acc.addMonomial (predAt i m) ((e : R) * c))
    0

/-- Homogeneous component of total degree `d`. -/
def homogeneousComponent [Lean.Grind.Semiring R] [DecidableEq R]
    (d : Nat) (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.restrictBy fun m => decide (Mono.degree m = d)

/-- General substitution, mapping coefficients through `f` and variables
through `g`. -/
def bind [Zero R] [Lean.Grind.Semiring S] [DecidableEq S]
    (f : R → S) (g : Fin n → MvPoly k S targetCmp)
    (p : MvPoly n R cmp) : MvPoly k S targetCmp :=
  p.foldTerms
    (fun acc m c => acc + C (f c) * Mono.prod g m)
    0

/-- Substitute polynomials for variables without changing the coefficient
type. -/
def subst [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R targetCmp)
    (p : MvPoly n R cmp) : MvPoly k R targetCmp :=
  bind id f p

/-- Compatibility spelling for same-coefficient substitution. -/
def bind₁ [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R targetCmp)
    (p : MvPoly n R cmp) : MvPoly k R targetCmp :=
  subst f p

/-- Reconstruct a polynomial by summing its ordered term iteration. -/
def sumToIter [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  ofTerms p.termsList

@[simp] theorem sumToIter_eq [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) :
    sumToIter p = p := by
  apply ext
  intro m
  unfold sumToIter
  rw [coeff_ofTerms, coeff_terms]

theorem coeff_reorder [Lean.Grind.Semiring R] [DecidableEq R]
    (cmp' : Mono n → Mono n → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (reorder cmp' p) = coeff m p := by
  unfold reorder
  rw [coeff_ofTerms, coeff_terms]

theorem coeff_rename [Lean.Grind.Semiring R] [DecidableEq R]
    (cmp' : Mono k → Mono k → Ordering)
    [Std.TransCmp cmp'] [Std.LawfulEqCmp cmp']
    (f : Fin n → Fin k) (m : Mono k) (p : MvPoly n R cmp) :
    coeff m (rename cmp' f p) =
      p.termsList.foldl
        (fun acc term => if Mono.rename f term.1 = m then acc + term.2 else acc) 0 := by
  have aux : ∀ (ts : List (Mono n × R)) (init : MvPoly k R cmp'),
      coeff m
          (ts.foldl
            (fun acc t => acc.addMonomial (Mono.rename f t.1) t.2)
            init) =
        ts.foldl
          (fun acc t =>
            if Mono.rename f t.1 = m then acc + t.2 else acc)
          (coeff m init) := by
    intro ts
    induction ts with
    | nil =>
      intro init
      rfl
    | cons t ts ih =>
      intro init
      rw [List.foldl_cons, ih]
      by_cases ht : Mono.rename f t.1 = m
      · simp [ht, coeff_addMonomial]
      · have hmt : m ≠ Mono.rename f t.1 := fun h => ht h.symm
        simp [ht, hmt, coeff_addMonomial]
  unfold rename foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList, aux, coeff_zero]
  rfl

theorem coeff_derivative [Lean.Grind.Semiring R] [DecidableEq R]
    (i : Fin n) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (derivative i p) =
      ((Mono.degreeOf i m + 1 : Nat) : R) * coeff (Mono.succAt i m) p := by
  let scale : R := ((Mono.degreeOf i m + 1 : Nat) : R)
  have aux : ∀ (ts : List (Mono n × R)) (init : MvPoly n R cmp),
      coeff m
          (ts.foldl
            (fun acc t =>
              let e := Mono.degreeOf i t.1
              if e = 0 then acc
              else acc.addMonomial (predAt i t.1) ((e : R) * t.2))
            init) =
        ts.foldl
          (fun acc t =>
            let e := Mono.degreeOf i t.1
            if e = 0 then acc
            else if m = predAt i t.1 then acc + (e : R) * t.2 else acc)
          (coeff m init) := by
    intro ts
    induction ts with
    | nil =>
      intro init
      rfl
    | cons t ts ih =>
      intro init
      rw [List.foldl_cons, ih]
      by_cases he : Mono.degreeOf i t.1 = 0
      · simp [he]
      · by_cases hm : m = predAt i t.1
        · simp [he, hm, coeff_addMonomial]
        · have hmp : m ≠ predAt i t.1 := hm
          simp [he, hmp, coeff_addMonomial]
  have step (acc : R) (t : Mono n × R) :
      (let e := Mono.degreeOf i t.1
        if e = 0 then acc
        else if m = predAt i t.1 then acc + (e : R) * t.2 else acc) =
      if t.1 = Mono.succAt i m then acc + scale * t.2 else acc := by
    rcases t with ⟨t, c⟩
    by_cases ht : t = Mono.succAt i m
    · subst t
      simp [scale]
    · by_cases he : Mono.degreeOf i t = 0
      · simp [he, ht]
      · have hpred : m ≠ predAt i t := by
          intro h
          have : t = Mono.succAt i m :=
            (predAt_eq_iff i m t he).mp h.symm
          exact ht this
        simp [he, hpred, ht]
  have filter_fold : ∀ (ts : List (Mono n × R)) (init : R),
      ts.foldl
          (fun acc t =>
            if t.1 = Mono.succAt i m then acc + scale * t.2 else acc)
          init =
        (ts.filter fun t => t.1 = Mono.succAt i m).foldl
          (fun acc t => acc + scale * t.2) init := by
    intro ts
    induction ts with
    | nil =>
      intro init
      rfl
    | cons t ts ih =>
      intro init
      rw [List.foldl_cons]
      by_cases ht : t.1 = Mono.succAt i m
      · simp [ht, ih]
      · simp [ht, ih]
  have scale_fold : ∀ (ts : List (Mono n × R)) (init : R),
      ts.foldl (fun acc t => acc + scale * t.2) (scale * init) =
        scale * ts.foldl (fun acc t => acc + t.2) init := by
    intro ts
    induction ts with
    | nil =>
      intro init
      rfl
    | cons t ts ih =>
      intro init
      rw [List.foldl_cons, ← Lean.Grind.Semiring.left_distrib, ih,
        List.foldl_cons]
  unfold derivative foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList, aux]
  rw [coeff_zero]
  simp only [step]
  rw [filter_fold]
  change
    (p.termsInternal.toList.filter fun t => t.1 = Mono.succAt i m).foldl
        (fun acc t => acc + scale * t.2) 0 =
      scale * coeff (Mono.succAt i m) p
  rw [← Lean.Grind.Semiring.mul_zero scale, scale_fold]
  congr 1
  simpa [termsList] using coeff_terms (Mono.succAt i m) p

theorem coeff_homogeneousComponent [Lean.Grind.Semiring R] [DecidableEq R]
    (d : Nat) (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (homogeneousComponent d p) =
      if Mono.degree m = d then coeff m p else 0 := by
  unfold homogeneousComponent
  rw [coeff_restrictBy]
  simp

theorem subst_eq [Lean.Grind.Semiring R] [DecidableEq R]
    (f : Fin n → MvPoly k R targetCmp) (p : MvPoly n R cmp) :
    subst f p =
      p.termsList.foldl
        (fun acc term => acc + C term.2 * Mono.prod f term.1) 0 := by
  unfold subst bind foldTerms
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  unfold termsList
  rfl

theorem partialEval_eq_subst [Lean.Grind.Semiring R] [DecidableEq R]
    (s : Fin n → Option R) (p : MvPoly n R cmp) :
    partialEval s p =
      subst (targetCmp := cmp)
        (fun i => match s i with | some x => C x | none => X i) p := by
  sorry

end Hex.MvPoly
