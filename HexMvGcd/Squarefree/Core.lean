/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvGcd.Squarefree.Basic

@[expose] public section
set_option backward.proofsInPublic true

/-!
Squarefree factor merging and its structural invariants.
-/

namespace Hex.MvPoly

universe u

attribute [local instance] Lean.Grind.Semiring.natCast
attribute [local instance] Lean.Grind.Ring.intCast

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]
  [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
  [GcdProducer R]

/-- Merge one factor into the multiplicity-sorted accumulator, multiplying
factors when the recursive content decomposition and the main-variable Yun
decomposition contribute at the same multiplicity. -/
def mergeSqfFactor (entry : SqfFactor n R cmp) :
    List (SqfFactor n R cmp) → List (SqfFactor n R cmp)
  | [] => [entry]
  | head :: tail =>
      if entry.multiplicity < head.multiplicity then entry :: head :: tail
      else if entry.multiplicity = head.multiplicity then
        { factor := entry.factor * head.factor
          multiplicity := entry.multiplicity } :: tail
      else head :: mergeSqfFactor entry tail

def sqfProduct (factors : List (SqfFactor n R cmp)) :
    MvPoly n R cmp :=
  factors.foldl (fun acc factor =>
    acc * factor.factor ^ factor.multiplicity) 1

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_from (factors : List (SqfFactor n R cmp))
    (start : MvPoly n R cmp) :
    factors.foldl (fun acc factor =>
      acc * factor.factor ^ factor.multiplicity) start =
      start * sqfProduct factors := by
  induction factors generalizing start with
  | nil =>
      change start = start * 1
      exact (MvPoly.mul_one start).symm
  | cons factor factors ih =>
      simp only [List.foldl_cons]
      rw [ih]
      change (start * factor.factor ^ factor.multiplicity) *
          sqfProduct factors =
        start * (factors.foldl
          (fun acc factor => acc * factor.factor ^ factor.multiplicity)
          (1 * factor.factor ^ factor.multiplicity))
      rw [ih]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
@[simp] theorem sqfProduct_nil :
    sqfProduct ([] : List (SqfFactor n R cmp)) = 1 := rfl

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_cons (factor : SqfFactor n R cmp)
    (factors : List (SqfFactor n R cmp)) :
    sqfProduct (factor :: factors) =
      factor.factor ^ factor.multiplicity * sqfProduct factors := by
  unfold sqfProduct
  rw [List.foldl_cons, sqfProduct_from]
  exact congrArg (fun x => x * sqfProduct factors)
    (MvPoly.one_mul _)

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem sqfProduct_merge (entry : SqfFactor n R cmp)
    (factors : List (SqfFactor n R cmp)) :
    sqfProduct (mergeSqfFactor entry factors) =
      entry.factor ^ entry.multiplicity * sqfProduct factors := by
  induction factors with
  | nil =>
      rw [mergeSqfFactor, sqfProduct_cons, sqfProduct_nil]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · rw [sqfProduct_cons, sqfProduct_cons]
      · split
        · rename_i heq
          have hpow : (entry.factor * head.factor) ^ entry.multiplicity =
              entry.factor ^ entry.multiplicity *
                head.factor ^ entry.multiplicity :=
            Lean.Grind.CommSemiring.mul_pow _ _ _
          rw [sqfProduct_cons, sqfProduct_cons]
          rw [hpow, heq]
          grind
        · rw [sqfProduct_cons, sqfProduct_cons, ih]
          grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_merge_fold
    (entries acc : List (SqfFactor n R cmp)) :
    sqfProduct (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) =
      sqfProduct entries * sqfProduct acc := by
  induction entries generalizing acc with
  | nil =>
      rw [List.foldl_nil, sqfProduct_nil, MvPoly.one_mul]
  | cons entry entries ih =>
      rw [List.foldl_cons, ih, sqfProduct_merge]
      rw [sqfProduct_cons]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_append
    (left right : List (SqfFactor n R cmp)) :
    sqfProduct (left ++ right) = sqfProduct left * sqfProduct right := by
  induction left with
  | nil => rw [List.nil_append, sqfProduct_nil, MvPoly.one_mul]
  | cons factor factors ih =>
      rw [List.cons_append, sqfProduct_cons, sqfProduct_cons, ih]
      grind

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem constIn_C
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (c : R) :
    constIn (cmp := order) i lowerOrder (C c) = C c := by
  apply MvPoly.ext
  intro monomial
  unfold constIn
  rw [← insertVar_removeVar i monomial, ofUnivariate_coeff,
    DensePoly.coeff_C, insertVar_removeVar]
  by_cases hdegree : Mono.degreeOf i monomial = 0
  · rw [ite_eq_left hdegree, coeff_C, coeff_C]
    have hzero : insertVar i 0 (Mono.zero : Mono m) = Mono.zero := by
      apply Vector.ext
      intro j hj
      simp [insertVar, Mono.zero]
    have hmonomial :
        monomial = Mono.zero ↔ removeVar i monomial = Mono.zero := by
      constructor
      · intro h
        subst monomial
        simp [removeVar, Mono.zero]
      · intro h
        calc
          monomial = insertVar i (Mono.degreeOf i monomial)
              (removeVar i monomial) := (insertVar_removeVar i monomial).symm
          _ = insertVar i 0 Mono.zero := by rw [hdegree, h]
          _ = Mono.zero := hzero
    simp only [hmonomial]
  · rw [ite_eq_right hdegree]
    have hmonomial : monomial ≠ Mono.zero := by
      intro h
      subst monomial
      exact hdegree (by
        unfold Mono.degreeOf
        exact Mono.getElem_zero i)
    change coeff (removeVar i monomial) (0 : MvPoly m R lowerOrder) =
      coeff monomial (C c : MvPoly (m + 1) R order)
    rw [coeff_zero, coeff_C, ite_eq_right hmonomial]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem constIn_pow
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (p : MvPoly m R lowerOrder) :
    ∀ k : Nat,
      constIn (cmp := order) i lowerOrder (p ^ k) =
        constIn i lowerOrder p ^ k := by
  intro k
  induction k with
  | zero => rw [MvPoly.pow_zero, MvPoly.pow_zero, constIn_one]
  | succ k ih =>
      rw [MvPoly.pow_succ, MvPoly.pow_succ, constIn_mul, ih]

omit [Dvd R] [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem sqfProduct_map_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) (factors : List (SqfFactor m R lowerOrder)) :
    sqfProduct (factors.map fun factor =>
      { factor := constIn (cmp := order) i lowerOrder factor.factor
        multiplicity := factor.multiplicity }) =
      constIn i lowerOrder (sqfProduct factors) := by
  induction factors with
  | nil => rw [List.map_nil, sqfProduct_nil, sqfProduct_nil, constIn_one]
  | cons factor factors ih =>
      rw [List.map_cons, sqfProduct_cons, sqfProduct_cons, ih,
        ← constIn_pow, ← constIn_mul]

private theorem eq_constIn_of_dvd
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {d : MvPoly (m + 1) R order}
    {r : MvPoly m R lowerOrder} (hr : r ≠ 0)
    (hdiv : d ∣ constIn (cmp := order) i lowerOrder r) :
    ∃ c : MvPoly m R lowerOrder, d = constIn i lowerOrder c := by
  rcases hdiv with ⟨q, hproduct⟩
  let dv := toUnivariate i lowerOrder d
  let qv := toUnivariate i lowerOrder q
  have hview : qv * dv = DensePoly.C r := by
    calc
      qv * dv = toUnivariate i lowerOrder (q * d) :=
        (toUnivariate_mul i q d).symm
      _ = DensePoly.C r := by rw [← hproduct, toUnivariate_constIn]
  have hconstant0 : DensePoly.C r ≠
      (0 : DensePoly (MvPoly m R lowerOrder)) := by
    intro hzero
    have hsize := congrArg DensePoly.size hzero
    rw [DensePoly.size_C_of_ne_zero hr, DensePoly.size_zero] at hsize
    omega
  have hproduct0 : qv * dv ≠ 0 := by rw [hview]; exact hconstant0
  have hqv0 : qv ≠ 0 := by
    intro hzero
    apply hproduct0
    rw [hzero, DensePoly.zero_mul]
  have hdv0 : dv ≠ 0 := by
    intro hzero
    apply hproduct0
    rw [DensePoly.mul_comm_poly qv, hzero, DensePoly.zero_mul]
  have hqpos : 0 < qv.size := Nat.pos_of_ne_zero fun hzero =>
    hqv0 ((DensePoly.size_eq_zero_iff qv).mp hzero)
  have hdpos : 0 < dv.size := Nat.pos_of_ne_zero fun hzero =>
    hdv0 ((DensePoly.size_eq_zero_iff dv).mp hzero)
  have htop : qv.leadingCoeff * dv.leadingCoeff ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div qv.leadingCoeff dv.leadingCoeff hzero with
      hq | hd
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqpos hq
    · exact DensePoly.leadingCoeff_ne_zero_of_pos_size dv hdpos hd
  have hsize := DensePoly.size_mul_of_top_ne qv dv hqpos hdpos htop
  have hdle : dv.size ≤ 1 := by
    rw [hview, DensePoly.size_C_of_ne_zero hr] at hsize
    omega
  let c := dv.coeff 0
  have hdense : dv = DensePoly.C c := by
    apply DensePoly.ext_coeff
    intro k
    rw [DensePoly.coeff_C]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk]
      exact DensePoly.coeff_eq_zero_of_size_le dv (by omega)
  refine ⟨c, ?_⟩
  calc
    d = ofUnivariate (cmp := order) i lowerOrder dv :=
      (ofUnivariate_toUnivariate i d).symm
    _ = ofUnivariate (cmp := order) i lowerOrder (DensePoly.C c) := by
      rw [hdense]
    _ = constIn i lowerOrder c := rfl

private theorem coeff_dvd_of_constIn_dvd
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {c : MvPoly m R lowerOrder}
    {d f : MvPoly (m + 1) R order}
    (hd : d = constIn i lowerOrder c) (hdf : d ∣ f) (k : Nat) :
    c ∣ (toUnivariate i lowerOrder f).coeff k := by
  rcases hdf with ⟨q, hq⟩
  refine ⟨(toUnivariate i lowerOrder q).coeff k, ?_⟩
  calc
    (toUnivariate i lowerOrder f).coeff k =
        (toUnivariate i lowerOrder (q * d)).coeff k := by rw [hq]
    _ = (toUnivariate i lowerOrder (constIn i lowerOrder c * q)).coeff k := by
      rw [hd, MvPoly.mul_comm q]
    _ = c * (toUnivariate i lowerOrder q).coeff k :=
      coeff_constIn_mul i c q k
    _ = (toUnivariate i lowerOrder q).coeff k * c := MvPoly.mul_comm _ _

private theorem common_coefficient {p : MvPoly n R cmp} {d : R}
    (hd : ∀ c, c ∈ coefficientList p → d ∣ c) :
    ∀ m, d ∣ coeff m p := by
  intro m
  by_cases hm : m ∈ p.monomials
  · rcases List.mem_map.mp hm with ⟨term, hterm, hmono⟩
    rcases term with ⟨termMono, termCoeff⟩
    simp only at hmono
    subst termMono
    rw [coeff_eq_of_mem_terms p hterm]
    apply hd termCoeff
    exact List.mem_map.mpr ⟨(m, termCoeff), hterm, rfl⟩
  · rw [coeff_eq_zero_of_not_mem m p hm]
    apply (LawfulGcdOps.dvd_iff d 0).mpr
    exact ⟨0, (Lean.Grind.Semiring.mul_zero d).symm⟩

theorem primitive_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : Primitive p) : Primitive (constIn (cmp := order) i lowerOrder p) := by
  intro d hd
  apply hp d
  intro c hc
  rcases List.mem_map.mp hc with ⟨term, hterm, rfl⟩
  rcases term with ⟨monomial, coefficient⟩
  have hcommon := common_coefficient hd (insertVar i 0 monomial)
  have hcoefficient := coeff_eq_of_mem_terms p hterm
  have hembedCoeff :
      coeff monomial p = coeff (insertVar i 0 monomial)
        (constIn (cmp := order) i lowerOrder p) := by
    calc
      coeff monomial p =
          coeff monomial
            ((toUnivariate i lowerOrder
              (constIn (cmp := order) i lowerOrder p)).coeff 0) := by
        rw [toUnivariate_constIn, DensePoly.coeff_C, ite_eq_left rfl]
      _ = coeff (insertVar i 0 monomial)
            (constIn (cmp := order) i lowerOrder p) :=
        toUnivariate_coeff i _ 0 monomial
  rw [← hcoefficient]
  rw [hembedCoeff]
  exact hcommon

omit [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
theorem isConst_of_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : IsConst (constIn (cmp := order) i lowerOrder p)) : IsConst p := by
  let c := coeff Mono.zero (constIn (cmp := order) i lowerOrder p)
  have heq : constIn (cmp := order) i lowerOrder p = C c :=
    eq_C_of_vars_eq_nil _ hp
  have heq' : constIn (cmp := order) i lowerOrder p =
      constIn i lowerOrder (C c) := by rw [constIn_C]; exact heq
  have hpC : p = C c := constIn_injective i heq'
  rw [hpC]
  exact isConst_C c

omit [BezoutOps R] [LawfulGcdOps R] [LawfulBezoutOps R]
    [GcdProducer R] in
private theorem isConst_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder} (hp : IsConst p) :
    IsConst (constIn (cmp := order) i lowerOrder p) := by
  let c := coeff Mono.zero p
  have hpC : p = C c := eq_C_of_vars_eq_nil p hp
  rw [hpC, constIn_C]
  exact isConst_C c

theorem squarefree_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {p : MvPoly m R lowerOrder}
    (hp : Squarefree p) :
    Squarefree (constIn (cmp := order) i lowerOrder p) := by
  refine ⟨fun hzero => hp.1 (constIn_injective i (hzero.trans (constIn_zero i).symm)), ?_⟩
  intro d hsquare
  have hp0 := hp.1
  have hdDvd : d ∣ constIn (cmp := order) i lowerOrder p := by
    rcases hsquare with ⟨q, hq⟩
    refine ⟨q * d, ?_⟩
    calc
      constIn (cmp := order) i lowerOrder p = q * (d * d) := hq
      _ = (q * d) * d := by grind
  rcases eq_constIn_of_dvd i hp0 hdDvd with ⟨c, hd⟩
  have hcSquare : c * c ∣ p := by
    have hconstSquare : d * d =
        constIn (cmp := order) i lowerOrder (c * c) := by
      rw [hd, constIn_mul]
    have hdiv : constIn (cmp := order) i lowerOrder (c * c) ∣
        constIn i lowerOrder p := by rw [← hconstSquare]; exact hsquare
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl hdiv 0
    simpa using hcoeff
  rw [hd]
  exact isConst_constIn i (hp.2 c hcSquare)

theorem coprime_constIn_of_content_one
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {a : MvPoly m R lowerOrder}
    {b : MvPoly (m + 1) R order} (ha0 : a ≠ 0)
    (hbContent : contentIn i lowerOrder b = 1) :
    ∀ d, d ∣ constIn (cmp := order) i lowerOrder a → d ∣ b →
      polyIsUnit d = true := by
  intro d hdA hdB
  rcases eq_constIn_of_dvd i ha0 hdA with ⟨c, hd⟩
  have hcContent : c ∣ contentIn i lowerOrder b := by
    apply dvd_contentIn i lowerOrder b c
    intro k
    exact coeff_dvd_of_constIn_dvd i hd hdB k
  rw [hbContent] at hcContent
  rcases hcContent with ⟨v, hv⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨constIn (cmp := order) i lowerOrder v, ?_⟩
  rw [hd, ← constIn_mul]
  have hcv : c * v = 1 := by
    calc
      c * v = v * c := MvPoly.mul_comm ..
      _ = 1 := hv.symm
  rw [hcv, constIn_one]

theorem coprime_constIn
    {m : Nat}
    {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    {lowerOrder : Mono m → Mono m → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    [Std.TransCmp lowerOrder] [Std.LawfulEqCmp lowerOrder]
    [IsMonomialOrder order] [IsMonomialOrder lowerOrder]
    (i : Fin (m + 1)) {a b : MvPoly m R lowerOrder} (ha0 : a ≠ 0)
    (hab : ∀ d, d ∣ a → d ∣ b → polyIsUnit d = true) :
    ∀ d, d ∣ constIn (cmp := order) i lowerOrder a →
      d ∣ constIn (cmp := order) i lowerOrder b → polyIsUnit d = true := by
  intro d hdA hdB
  rcases eq_constIn_of_dvd i ha0 hdA with ⟨c, hd⟩
  have hcA : c ∣ a := by
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl (hd ▸ hdA) 0
    simpa using hcoeff
  have hcB : c ∣ b := by
    have hcoeff := coeff_dvd_of_constIn_dvd i rfl (hd ▸ hdB) 0
    simpa using hcoeff
  rcases (polyIsUnit_iff c).mp (hab c hcA hcB) with ⟨v, hv⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨constIn (cmp := order) i lowerOrder v, ?_⟩
  rw [hd, ← constIn_mul]
  rw [hv, constIn_one]

private theorem squarefree_mul_of_coprime [IsMonomialOrder cmp]
    {p q : MvPoly n R cmp} (hp : Squarefree p) (hq : Squarefree q)
    (hcoprime : ∀ d, d ∣ p → d ∣ q → polyIsUnit d = true) :
    Squarefree (p * q) := by
  have hpq0 : p * q ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p q hzero with hp0 | hq0
    · exact hp.1 hp0
    · exact hq.1 hq0
  refine ⟨hpq0, ?_⟩
  intro r hrr
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    rcases hrr with ⟨a, ha⟩
    rw [MvPoly.zero_mul, MvPoly.mul_zero] at ha
    exact hpq0 ha
  let a := gcd r p
  let b := quotient r a
  let p₁ := quotient p a
  rcases gcd_quotients (b := r) (d := p) hr0 with
    ⟨ha0, hba, hp₁a, hcopBP⟩
  change a ≠ 0 at ha0
  change b * a = r at hba
  change p₁ * a = p at hp₁a
  have hb0 : b ≠ 0 := by
    intro hb
    apply hr0
    rw [← hba, hb, MvPoly.zero_mul]
  have haP : a ∣ p := gcd_dvd_right r p
  have hcopQA : ∀ e, e ∣ q → e ∣ a → ∃ u, e * u = 1 := by
    intro e heQ heA
    exact (polyIsUnit_iff e).mp
      (hcoprime e (Hex.dvdTrans heA haP) heQ)
  rcases hrr with ⟨x, hx⟩
  have hp₁q : p₁ * q = (x * b * b) * a := by
    have hzero : a * (p₁ * q - (x * b * b) * a) = 0 := by
      calc
        a * (p₁ * q - (x * b * b) * a) =
            (p₁ * a) * q - x * ((b * a) * (b * a)) := by grind
        _ = p * q - x * (r * r) := by rw [hp₁a, hba]
        _ = 0 := by rw [hx]; grind
    rcases GcdDomainLaws.no_zero_div a _ hzero with hzero | hcancel
    · exact False.elim (ha0 hzero)
    · grind
  have haP₁Q : a ∣ p₁ * q := ⟨x * b * b, hp₁q⟩
  have haP₁A : a ∣ p₁ * a := ⟨p₁, rfl⟩
  have haP₁ : a ∣ p₁ :=
    CoprimeCancelLaws.cancel_coprime p₁ q a a hcopQA haP₁Q haP₁A
  have haSquareP : a * a ∣ p := by
    rcases haP₁ with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      p = p₁ * a := hp₁a.symm
      _ = (t * a) * a := by rw [ht]
      _ = t * (a * a) := by grind
  have haConst : IsConst a := hp.2 a haSquareP
  have hbSquareP₁Q : b * b ∣ p₁ * q := by
    refine ⟨x * a, ?_⟩
    calc
      p₁ * q = (x * b * b) * a := hp₁q
      _ = (x * a) * (b * b) := by grind
  have hbP₁Q : b ∣ p₁ * q := by
    exact Hex.dvdTrans
      (show b ∣ b * b from ⟨b, rfl⟩) hbSquareP₁Q
  have hbQB : b ∣ q * b := ⟨q, rfl⟩
  have hcopP₁B : ∀ e, e ∣ p₁ → e ∣ b → ∃ u, e * u = 1 := by
    intro e heP₁ heB
    exact (polyIsUnit_iff e).mp (hcopBP e heB heP₁)
  have hbQ : b ∣ q :=
    CoprimeCancelLaws.cancel_coprime q p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q) hbQB
  rcases hbQ with ⟨q₁, hq₁⟩
  rcases hbSquareP₁Q with ⟨y, hy⟩
  have hbP₁Q₁ : b ∣ p₁ * q₁ := by
    have hzero : b * (p₁ * q₁ - y * b) = 0 := by
      calc
        b * (p₁ * q₁ - y * b) = p₁ * (q₁ * b) - y * (b * b) := by
          grind
        _ = p₁ * q - y * (b * b) := by rw [hq₁]
        _ = 0 := by rw [hy]; grind
    rcases GcdDomainLaws.no_zero_div b _ hzero with hzero | hcancel
    · exact False.elim (hb0 hzero)
    · refine ⟨y, ?_⟩
      grind
  have hbQ₁B : b ∣ q₁ * b := ⟨q₁, rfl⟩
  have hbQ₁ : b ∣ q₁ :=
    CoprimeCancelLaws.cancel_coprime q₁ p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q₁) hbQ₁B
  have hbSquareQ : b * b ∣ q := by
    rcases hbQ₁ with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      q = q₁ * b := hq₁
      _ = (z * b) * b := by rw [hz]
      _ = z * (b * b) := by grind
  have hbConst : IsConst b := hq.2 b hbSquareQ
  let ca := coeff Mono.zero a
  let cb := coeff Mono.zero b
  have haC : a = C ca := eq_C_of_vars_eq_nil a haConst
  have hbC : b = C cb := eq_C_of_vars_eq_nil b hbConst
  have hrC : r = C (cb * ca) := by
    calc
      r = b * a := hba.symm
      _ = C cb * C ca := by rw [hbC, haC]
      _ = C (cb * ca) := C_mul_C cb ca
  rw [hrC]
  exact isConst_C _

private theorem coprime_mul_left [IsMonomialOrder cmp]
    {p q r : MvPoly n R cmp} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpr : ∀ d, d ∣ p → d ∣ r → polyIsUnit d = true)
    (hqr : ∀ d, d ∣ q → d ∣ r → polyIsUnit d = true) :
    ∀ d, d ∣ p * q → d ∣ r → polyIsUnit d = true := by
  intro d hdPQ hdR
  have hpq0 : p * q ≠ 0 := by
    intro hzero
    rcases GcdDomainLaws.no_zero_div p q hzero with hzero | hzero
    · exact hp0 hzero
    · exact hq0 hzero
  have hd0 : d ≠ 0 := by
    intro hzero
    subst d
    rcases hdPQ with ⟨a, ha⟩
    rw [MvPoly.mul_zero] at ha
    exact hpq0 ha
  let a := gcd d p
  let b := quotient d a
  let p₁ := quotient p a
  rcases gcd_quotients (b := d) (d := p) hd0 with
    ⟨ha0, hba, hp₁a, hcopBP⟩
  change a ≠ 0 at ha0
  change b * a = d at hba
  change p₁ * a = p at hp₁a
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hd0
    rw [← hba, hzero, MvPoly.zero_mul]
  have haP : a ∣ p := gcd_dvd_right d p
  have haD : a ∣ d := gcd_dvd_left d p
  have haR : a ∣ r := Hex.dvdTrans haD hdR
  have haUnit : polyIsUnit a = true := hpr a haP haR
  rcases hdPQ with ⟨x, hx⟩
  have hbP₁Q : b ∣ p₁ * q := by
    have hzero : a * (p₁ * q - x * b) = 0 := by
      calc
        a * (p₁ * q - x * b) = (p₁ * a) * q - x * (b * a) := by
          grind
        _ = p * q - x * d := by rw [hp₁a, hba]
        _ = 0 := by rw [hx]; grind
    rcases GcdDomainLaws.no_zero_div a _ hzero with hzero | hcancel
    · exact False.elim (ha0 hzero)
    · refine ⟨x, ?_⟩
      grind
  have hcopP₁B : ∀ e, e ∣ p₁ → e ∣ b → ∃ u, e * u = 1 := by
    intro e heP₁ heB
    exact (polyIsUnit_iff e).mp (hcopBP e heB heP₁)
  have hbQB : b ∣ q * b := ⟨q, rfl⟩
  have hbQ : b ∣ q :=
    CoprimeCancelLaws.cancel_coprime q p₁ b b hcopP₁B
      (by rw [MvPoly.mul_comm]; exact hbP₁Q) hbQB
  have hbD : b ∣ d := by
    refine ⟨a, ?_⟩
    rw [MvPoly.mul_comm]
    exact hba.symm
  have hbR : b ∣ r := Hex.dvdTrans hbD hdR
  have hbUnit : polyIsUnit b = true := hqr b hbQ hbR
  rcases (polyIsUnit_iff a).mp haUnit with ⟨ia, hia⟩
  rcases (polyIsUnit_iff b).mp hbUnit with ⟨ib, hib⟩
  apply (polyIsUnit_iff d).mpr
  refine ⟨ia * ib, ?_⟩
  calc
    d * (ia * ib) = (b * ib) * (a * ia) := by rw [← hba]; grind
    _ = 1 := by rw [hib, hia, MvPoly.one_mul]

private theorem nonconstant_mul_left [NatNoZero R]
    {m : Nat} {order : Mono (m + 1) → Mono (m + 1) → Ordering}
    [Std.TransCmp order] [Std.LawfulEqCmp order]
    {p q : MvPoly (m + 1) R order} (hp : ¬ IsConst p) (hq0 : q ≠ 0) :
    ¬ IsConst (p * q) := by
  intro hpq
  cases hvars : p.vars with
  | nil => exact hp hvars
  | cons i tail =>
      have hi : i ∈ p.vars := by rw [hvars]; simp
      let pv := toUnivariate i Mono.lex p
      let qv := toUnivariate i Mono.lex q
      have hpvSize : 1 < pv.size := view_size_gt_one_of_mem_vars i p hi
      have hqv0 : qv ≠ 0 := by
        intro hzero
        apply hq0
        calc
          q = ofUnivariate i Mono.lex qv :=
            (ofUnivariate_toUnivariate i q).symm
          _ = 0 := by rw [hzero]; rfl
      have hqvPos : 0 < qv.size :=
        Nat.pos_of_ne_zero
          (fun h => hqv0 ((DensePoly.size_eq_zero_iff qv).mp h))
      have hpvPos : 0 < pv.size := by omega
      have htop : pv.leadingCoeff * qv.leadingCoeff ≠
          (0 : MvPoly m R Mono.lex) := by
        intro hzero
        rcases GcdDomainLaws.no_zero_div _ _ hzero with hl | hr
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size pv hpvPos) hl
        · exact (DensePoly.leadingCoeff_ne_zero_of_pos_size qv hqvPos) hr
      have hsize := DensePoly.size_mul_of_top_ne pv qv hpvPos hqvPos htop
      have hpqC : p * q = C (coeff Mono.zero (p * q)) :=
        eq_C_of_vars_eq_nil (p * q) hpq
      have hsizeC := congrArg
        (fun f => (toUnivariate i Mono.lex f).size) hpqC
      rw [toUnivariate_mul, hsize] at hsizeC
      have hCle :
          (toUnivariate i Mono.lex
            (C (coeff Mono.zero (p * q)) : MvPoly (m + 1) R order)).size ≤ 1 := by
        rw [← constIn_C (order := order) (lowerOrder := Mono.lex) i,
          toUnivariate_constIn]
        exact DensePoly.size_C_le_one _
      omega

private theorem nonconstant_mul [NatNoZero R]
    {p q : MvPoly n R cmp} (hp : ¬ IsConst p) (hq0 : q ≠ 0) :
    ¬ IsConst (p * q) := by
  cases n with
  | zero =>
      exfalso
      apply hp
      unfold IsConst
      rw [vars_eq]
      simp [Mono.support]
  | succ m => exact nonconstant_mul_left hp hq0

def CoprimePoly (p q : MvPoly n R cmp) : Prop :=
  ∀ d, d ∣ p → d ∣ q → polyIsUnit d = true

private theorem coprimePoly_symm {p q : MvPoly n R cmp}
    (hpq : CoprimePoly p q) : CoprimePoly q p := by
  intro d hdq hdp
  exact hpq d hdp hdq

private theorem coprimePoly_mul_left [IsMonomialOrder cmp]
    {p q r : MvPoly n R cmp} (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    (hpr : CoprimePoly p r) (hqr : CoprimePoly q r) :
    CoprimePoly (p * q) r :=
  coprime_mul_left hp0 hq0 hpr hqr

structure FactorProperties
    (factors : List (SqfFactor n R cmp)) : Prop where
  squarefree : ∀ factor ∈ factors, Squarefree factor.factor
  primitive : ∀ factor ∈ factors, Primitive factor.factor
  nonconstant : ∀ factor ∈ factors, ¬ IsConst factor.factor
  pairwise : factors.Pairwise fun left right =>
    CoprimePoly left.factor right.factor

theorem properties_nil :
    FactorProperties ([] : List (SqfFactor n R cmp)) :=
  { squarefree := by simp
    primitive := by simp
    nonconstant := by simp
    pairwise := by simp }

theorem coprime_of_mem
    {factors : List (SqfFactor n R cmp)}
    (hpairwise : factors.Pairwise fun left right =>
      CoprimePoly left.factor right.factor) :
    ∀ left ∈ factors, ∀ right ∈ factors, left ≠ right →
      CoprimePoly left.factor right.factor := by
  induction factors with
  | nil => simp
  | cons head tail ih =>
      have hsource := List.pairwise_cons.mp hpairwise
      intro left hleft right hright hne
      rcases List.mem_cons.mp hleft with hleftEq | hleft
      · subst left
        rcases List.mem_cons.mp hright with hrightEq | hright
        · subst right
          exact False.elim (hne rfl)
        · exact hsource.1 right hright
      · rcases List.mem_cons.mp hright with hrightEq | hright
        · subst right
          exact coprimePoly_symm (hsource.1 left hleft)
        · exact ih hsource.2 left hleft right hright hne

def CrossFactors (left right : List (SqfFactor n R cmp)) : Prop :=
  ∀ a ∈ left, ∀ b ∈ right, CoprimePoly a.factor b.factor

private theorem coprime_merge [IsMonomialOrder cmp]
    (entry : SqfFactor n R cmp)
    {factors : List (SqfFactor n R cmp)} {p : MvPoly n R cmp}
    (hentry0 : entry.factor ≠ 0)
    (hfactors0 : ∀ factor ∈ factors, factor.factor ≠ 0)
    (hentry : CoprimePoly p entry.factor)
    (hfactors : ∀ factor ∈ factors, CoprimePoly p factor.factor) :
    ∀ factor ∈ mergeSqfFactor entry factors,
      CoprimePoly p factor.factor := by
  induction factors with
  | nil =>
      intro factor hfactor
      simp only [mergeSqfFactor, List.mem_cons, List.not_mem_nil,
        or_false] at hfactor
      subst factor
      exact hentry
  | cons head tail ih =>
      have hhead0 := hfactors0 head (by simp)
      have htail0 : ∀ factor ∈ tail, factor.factor ≠ 0 := by
        intro factor hfactor
        exact hfactors0 factor (by simp [hfactor])
      have hhead := hfactors head (by simp)
      have htail : ∀ factor ∈ tail, CoprimePoly p factor.factor := by
        intro factor hfactor
        exact hfactors factor (by simp [hfactor])
      simp only [mergeSqfFactor]
      split
      · intro factor hfactor
        simp only [List.mem_cons] at hfactor
        rcases hfactor with rfl | hfactor
        · exact hentry
        · exact hfactors factor (by simp [hfactor])
      · split
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · apply coprimePoly_symm
            apply coprimePoly_mul_left hentry0 hhead0
            · exact coprimePoly_symm hentry
            · exact coprimePoly_symm hhead
          · exact htail factor hfactor
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · exact hhead
          · exact ih htail0 htail factor hfactor

private theorem properties_merge [NatNoZero R] [IsMonomialOrder cmp]
    (entry : SqfFactor n R cmp) {factors : List (SqfFactor n R cmp)}
    (hentrySqf : Squarefree entry.factor)
    (hentryPrimitive : Primitive entry.factor)
    (hentryNonconst : ¬ IsConst entry.factor)
    (hfactors : FactorProperties factors)
    (hcross : ∀ factor ∈ factors,
      CoprimePoly entry.factor factor.factor) :
    FactorProperties (mergeSqfFactor entry factors) := by
  induction factors with
  | nil =>
      simp only [mergeSqfFactor]
      exact
        { squarefree := by simpa
          primitive := by simpa
          nonconstant := by simpa
          pairwise := by simp }
  | cons head tail ih =>
      have hheadSqf := hfactors.squarefree head (by simp)
      have hheadPrimitive := hfactors.primitive head (by simp)
      have hheadNonconst := hfactors.nonconstant head (by simp)
      have htail : FactorProperties tail :=
        { squarefree := by
            intro factor hfactor
            exact hfactors.squarefree factor (by simp [hfactor])
          primitive := by
            intro factor hfactor
            exact hfactors.primitive factor (by simp [hfactor])
          nonconstant := by
            intro factor hfactor
            exact hfactors.nonconstant factor (by simp [hfactor])
          pairwise := (List.pairwise_cons.mp hfactors.pairwise).2 }
      have hheadTail : ∀ factor ∈ tail,
          CoprimePoly head.factor factor.factor :=
        (List.pairwise_cons.mp hfactors.pairwise).1
      have hentryHead := hcross head (by simp)
      have hentryTail : ∀ factor ∈ tail,
          CoprimePoly entry.factor factor.factor := by
        intro factor hfactor
        exact hcross factor (by simp [hfactor])
      simp only [mergeSqfFactor]
      split
      · exact
          { squarefree := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentrySqf
              · exact hfactors.squarefree factor
                  (by simpa only [List.mem_cons] using hfactor)
            primitive := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentryPrimitive
              · exact hfactors.primitive factor
                  (by simpa only [List.mem_cons] using hfactor)
            nonconstant := by
              intro factor hfactor
              simp only [List.mem_cons] at hfactor
              rcases hfactor with rfl | hfactor
              · exact hentryNonconst
              · exact hfactors.nonconstant factor
                  (by simpa only [List.mem_cons] using hfactor)
            pairwise := List.Pairwise.cons hcross hfactors.pairwise }
      · split
        · exact
            { squarefree := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact squarefree_mul_of_coprime hentrySqf hheadSqf hentryHead
                · exact htail.squarefree factor hfactor
              primitive := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact primitive_mul hentryPrimitive hheadPrimitive
                · exact htail.primitive factor hfactor
              nonconstant := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact nonconstant_mul hentryNonconst hheadSqf.1
                · exact htail.nonconstant factor hfactor
              pairwise := by
                apply List.Pairwise.cons
                · intro factor hfactor
                  exact coprimePoly_mul_left hentrySqf.1 hheadSqf.1
                    (hentryTail factor hfactor) (hheadTail factor hfactor)
                · exact htail.pairwise }
        · have hmerged := ih htail hentryTail
          exact
            { squarefree := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadSqf
                · exact hmerged.squarefree factor hfactor
              primitive := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadPrimitive
                · exact hmerged.primitive factor hfactor
              nonconstant := by
                intro factor hfactor
                simp only [List.mem_cons] at hfactor
                rcases hfactor with rfl | hfactor
                · exact hheadNonconst
                · exact hmerged.nonconstant factor hfactor
              pairwise := by
                apply List.Pairwise.cons
                · apply coprime_merge entry hentrySqf.1
                  · intro factor hfactor
                    exact (htail.squarefree factor hfactor).1
                  · exact coprimePoly_symm hentryHead
                  · exact hheadTail
                · exact hmerged.pairwise }

theorem properties_merge_fold [NatNoZero R]
    [IsMonomialOrder cmp]
    (entries acc : List (SqfFactor n R cmp))
    (hentries : FactorProperties entries)
    (hacc : FactorProperties acc)
    (hcross : CrossFactors entries acc) :
    FactorProperties (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa using hacc
  | cons entry entries ih =>
      have hentrySqf := hentries.squarefree entry (by simp)
      have hentryPrimitive := hentries.primitive entry (by simp)
      have hentryNonconst := hentries.nonconstant entry (by simp)
      have htail : FactorProperties entries :=
        { squarefree := by
            intro factor hfactor
            exact hentries.squarefree factor (by simp [hfactor])
          primitive := by
            intro factor hfactor
            exact hentries.primitive factor (by simp [hfactor])
          nonconstant := by
            intro factor hfactor
            exact hentries.nonconstant factor (by simp [hfactor])
          pairwise := (List.pairwise_cons.mp hentries.pairwise).2 }
      have hentryTail : ∀ factor ∈ entries,
          CoprimePoly entry.factor factor.factor :=
        (List.pairwise_cons.mp hentries.pairwise).1
      have hentryAcc : ∀ factor ∈ acc,
          CoprimePoly entry.factor factor.factor := by
        intro factor hfactor
        exact hcross entry (by simp) factor hfactor
      have hmerged := properties_merge entry hentrySqf hentryPrimitive
        hentryNonconst hacc hentryAcc
      apply ih (mergeSqfFactor entry acc) htail hmerged
      intro left hleft right hright
      exact coprime_merge entry hentrySqf.1
        (fun factor hfactor => (hacc.squarefree factor hfactor).1)
        (coprimePoly_symm (hentryTail left hleft))
        (fun factor hfactor => hcross left (by simp [hleft]) factor hfactor)
        right hright

def PositiveMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, 0 < factor.multiplicity

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem positive_merge (entry : SqfFactor n R cmp)
    (hentry : 0 < entry.multiplicity) {factors : List (SqfFactor n R cmp)}
    (hfactors : PositiveMultiplicities factors) :
    PositiveMultiplicities (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simpa [PositiveMultiplicities, mergeSqfFactor]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · simp_all [PositiveMultiplicities]
      · split
        · simp_all [PositiveMultiplicities]
        · simp_all [PositiveMultiplicities]

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
theorem positive_merge_fold (entries acc : List (SqfFactor n R cmp))
    (hentries : PositiveMultiplicities entries)
    (hacc : PositiveMultiplicities acc) :
    PositiveMultiplicities (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      have hentries' : 0 < entry.multiplicity ∧
          PositiveMultiplicities entries := by
        simpa [PositiveMultiplicities] using hentries
      apply ih
      · exact hentries'.2
      · apply positive_merge entry
        · exact hentries'.1
        · exact hacc

private def MultiplicitiesAbove (bound : Nat)
    (factors : List (SqfFactor n R cmp)) : Prop :=
  ∀ factor ∈ factors, bound < factor.multiplicity

def SortedMultiplicities (factors : List (SqfFactor n R cmp)) : Prop :=
  factors.Pairwise fun left right => left.multiplicity < right.multiplicity

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem above_merge (bound : Nat) (entry : SqfFactor n R cmp)
    (hentry : bound < entry.multiplicity) {factors : List (SqfFactor n R cmp)}
    (hfactors : MultiplicitiesAbove bound factors) :
    MultiplicitiesAbove bound (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simpa [MultiplicitiesAbove, mergeSqfFactor]
  | cons head tail ih =>
      simp only [mergeSqfFactor]
      split
      · simp_all [MultiplicitiesAbove]
      · split
        · simp_all [MultiplicitiesAbove]
        · simp_all [MultiplicitiesAbove]

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
private theorem sorted_merge (entry : SqfFactor n R cmp)
    {factors : List (SqfFactor n R cmp)}
    (hfactors : SortedMultiplicities factors) :
    SortedMultiplicities (mergeSqfFactor entry factors) := by
  induction factors with
  | nil => simp [SortedMultiplicities, mergeSqfFactor]
  | cons head tail ih =>
      have hsorted : MultiplicitiesAbove head.multiplicity tail ∧
          SortedMultiplicities tail := by
        simpa [MultiplicitiesAbove, SortedMultiplicities] using hfactors
      simp only [mergeSqfFactor]
      split <;> rename_i hlt
      · apply List.Pairwise.cons
        · intro factor hfactor
          simp only [List.mem_cons] at hfactor
          rcases hfactor with rfl | hfactor
          · exact hlt
          · exact Nat.lt_trans hlt (hsorted.1 factor hfactor)
        · exact hfactors
      · split <;> rename_i heq
        · apply List.Pairwise.cons
          · intro factor hfactor
            simpa [heq] using hsorted.1 factor hfactor
          · exact hsorted.2
        · apply List.Pairwise.cons
          · apply above_merge
            · omega
            · exact hsorted.1
          · exact ih hsorted.2

omit [DecidableEq R] [Dvd R] [BezoutOps R] [LawfulGcdOps R]
    [LawfulBezoutOps R] [GcdProducer R] in
theorem sorted_merge_fold (entries acc : List (SqfFactor n R cmp))
    (hacc : SortedMultiplicities acc) :
    SortedMultiplicities (entries.foldl
      (fun acc entry => mergeSqfFactor entry acc) acc) := by
  induction entries generalizing acc with
  | nil => simpa
  | cons entry entries ih =>
      simp only [List.foldl_cons]
      exact ih _ (sorted_merge entry hacc)

end Hex.MvPoly
