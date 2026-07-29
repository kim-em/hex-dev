/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
import HexBasic.List
public import HexMvPoly.Basic

@[expose] public section

/-!
Canonical sparse arithmetic for `Hex.MvPoly`.

Addition folds the smaller operation stream into one tree, and multiplication
uses a Gustavson-style double traversal with a single output accumulator.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

/-- Negation preserves nonzero coefficients in a ring. -/
theorem negCoeff_ne_zero [Lean.Grind.Ring R] (c : R) (hc : c ≠ 0) :
    -c ≠ 0 := by
  grind

variable [BEq R] [LawfulBEq R]

/-- Polynomial addition, combining equal monomials and deleting cancellations. -/
def add [Add R] [Zero R] [BEq R] [LawfulBEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  { termsInternal :=
      p.termsInternal.mergeWith?
        (fun _ a b =>
          let c := a + b
          if c = 0 then none else some c)
        q.termsInternal
    nonzeroInternal := by
      intro m
      rw [Std.ExtTreeMap.getElem?_mergeWith?]
      cases hp : p.termsInternal[m]? with
      | none =>
          cases hq : q.termsInternal[m]? with
          | none => simp [Std.ExtTreeMap.mergeValue?]
          | some b =>
              simpa [Std.ExtTreeMap.mergeValue?, hq] using q.nonzeroInternal m
      | some a =>
          cases hq : q.termsInternal[m]? with
          | none =>
              simpa [Std.ExtTreeMap.mergeValue?, hp] using p.nonzeroInternal m
          | some b =>
              simp only [Std.ExtTreeMap.mergeValue?]
              split <;> simp_all }

instance [Add R] [Zero R] [BEq R] [LawfulBEq R] :
    Add (MvPoly n R cmp) where
  add := add

/-- Coefficientwise negation, filtering any zero result in one tree pass. -/
def neg [Neg R] [Zero R] [BEq R] [LawfulBEq R]
    (p : MvPoly n R cmp) : MvPoly n R cmp :=
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  { termsInternal := p.termsInternal.filterMap fun _ c =>
      let c' := -c
      if c' = 0 then none else some c'
    nonzeroInternal := by
      intro m
      rw [Std.ExtTreeMap.getElem?_filterMap']
      cases hcoeff : p.termsInternal[m]? with
      | none => simp
      | some c =>
          simp only [Option.bind_some]
          split <;> simp_all }

instance [Neg R] [Zero R] [BEq R] [LawfulBEq R] :
    Neg (MvPoly n R cmp) where
  neg := neg

/-- Polynomial subtraction. -/
def sub [Add R] [Neg R] [Zero R] [BEq R] [LawfulBEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  add p (neg q)

instance [Add R] [Neg R] [Zero R] [BEq R] [LawfulBEq R] :
    Sub (MvPoly n R cmp) where
  sub := sub

/-- Polynomial multiplication. Every translated product term is accumulated
directly into one output map, so collisions and cancellations are normalized
as they arise. -/
def mul [Add R] [Mul R] [Zero R] [BEq R] [LawfulBEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc mp cp =>
      q.foldTerms
        (fun acc mq cq => acc.addMonomial (Mono.mul mp mq) (cp * cq))
        acc)
    0

instance [Add R] [Mul R] [Zero R] [BEq R] [LawfulBEq R] :
    Mul (MvPoly n R cmp) where
  mul := mul

/-- Multiplicative identity. -/
def one [Zero R] [One R] [BEq R] [LawfulBEq R] : MvPoly n R cmp :=
  C 1

instance [Zero R] [One R] [BEq R] [LawfulBEq R] :
    One (MvPoly n R cmp) where
  one := one

/-- Exponentiation by repeated squaring. -/
def npowBySq [Add R] [Mul R] [Zero R] [One R] [BEq R] [LawfulBEq R]
    (p : MvPoly n R cmp) : Nat → MvPoly n R cmp
  | 0 => 1
  | k + 1 =>
      let q := npowBySq p ((k + 1) / 2)
      let q2 := q * q
      if (k + 1) % 2 = 0 then q2 else q2 * p
termination_by k => k
decreasing_by omega

instance [Add R] [Mul R] [Zero R] [One R] [BEq R] [LawfulBEq R] :
    Pow (MvPoly n R cmp) Nat where
  pow := npowBySq

/-- The coefficient of one is one at the zero monomial and zero elsewhere. -/
@[simp] theorem coeff_one [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) :
    coeff m (1 : MvPoly n R cmp) =
      if m = Mono.zero then 1 else 0 := by
  change coeff m (C 1) = _
  exact coeff_C m 1

/-- Coefficients distribute over polynomial addition. -/
theorem coeff_add [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p + q) = coeff m p + coeff m q := by
  change ((add p q).termsInternal[m]?).getD 0 =
    p.termsInternal[m]?.getD 0 + q.termsInternal[m]?.getD 0
  unfold add
  rw [Std.ExtTreeMap.getElem?_mergeWith?]
  cases p.termsInternal[m]? <;> cases q.termsInternal[m]? <;>
    simp [Std.ExtTreeMap.mergeValue?, Lean.Grind.AddCommMonoid.zero_add,
      Lean.Grind.AddCommMonoid.add_zero] <;>
    split <;> simp_all

/-- Zero is a right identity for polynomial addition. -/
theorem add_zero [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : p + 0 = p := by
  apply ext
  intro m
  rw [coeff_add, coeff_zero, Lean.Grind.Semiring.add_zero]

/-- Zero is a left identity for polynomial addition. -/
theorem zero_add [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : 0 + p = p := by
  apply ext
  intro m
  rw [coeff_add, coeff_zero, Lean.Grind.AddCommMonoid.zero_add]

/-- Polynomial addition is commutative. -/
theorem add_comm [Lean.Grind.Semiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : p + q = q + p := by
  apply ext
  intro m
  rw [coeff_add, coeff_add, Lean.Grind.Semiring.add_comm]

/-- Polynomial addition is associative. -/
theorem add_assoc [Lean.Grind.Semiring R] [DecidableEq R]
    (p q r : MvPoly n R cmp) : (p + q) + r = p + (q + r) := by
  apply ext
  intro m
  simp only [coeff_add]
  rw [Lean.Grind.Semiring.add_assoc]

/-- Adding a monomial is ordinary addition by a monomial polynomial. -/
theorem addMonomial_eq [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (m : Mono n) (c : R) :
    p.addMonomial m c = p + monomial m c := by
  apply ext
  intro k
  rw [coeff_addMonomial, coeff_add, coeff_monomial]
  by_cases hkm : k = m
  · rw [if_pos hkm, if_pos hkm]
  · rw [if_neg hkm, if_neg hkm, Lean.Grind.Semiring.add_zero]

/-- Coefficients commute with polynomial negation. -/
theorem coeff_neg [Lean.Grind.Ring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (-p) = -coeff m p := by
  change coeff m (neg p) = -coeff m p
  unfold neg coeff coeff?
  rw [Std.ExtTreeMap.getElem?_filterMap']
  cases hcoeff : p.termsInternal[m]? with
  | none => exact Lean.Grind.AddCommGroup.neg_zero.symm
  | some c =>
      have hc : c ≠ 0 := by
        intro hzero
        apply p.nonzeroInternal m
        simpa [hzero] using hcoeff
      simp [negCoeff_ne_zero c hc]

/-- Coefficients distribute over polynomial subtraction. -/
theorem coeff_sub [Lean.Grind.Ring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p - q) = coeff m p - coeff m q := by
  change coeff m (p + (-q)) = coeff m p - coeff m q
  rw [coeff_add, coeff_neg, Lean.Grind.Ring.sub_eq_add_neg]

/-- A product coefficient is the convolution over monomial splittings. -/
theorem coeff_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p * q) =
      (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 := by
  let pairs : List ((Mono n × R) × (Mono n × R)) :=
    p.termsList.flatMap fun pt => q.termsList.map fun qt => (pt, qt)
  have hmul :
      mul p q =
        ofTerms (pairs.map fun t =>
          (Mono.mul t.1.1 t.2.1, t.1.2 * t.2.2)) := by
    unfold mul ofTerms foldTerms pairs termsList
    simp only [Std.ExtTreeMap.foldl_eq_foldl_toList, List.foldl_map,
      List.foldl_flatMap]
  have hpairsCoeff :
      coeff m (mul p q) =
        pairs.foldl
          (fun acc t =>
            acc + if Mono.mul t.1.1 t.2.1 = m then t.1.2 * t.2.2 else 0)
          0 := by
    rw [hmul, coeff_ofTerms, List.foldl_filter, List.foldl_map]
    apply List.foldl_congr
    intro acc t ht
    by_cases hterm : Mono.mul t.1.1 t.2.1 = m <;>
      simp [hterm, Lean.Grind.AddCommMonoid.add_zero]
  let keyPairs : List (Mono n × Mono n) :=
    pairs.map fun t => (t.1.1, t.2.1)
  have hpairsKeys :
      pairs.foldl
          (fun acc t =>
            acc + if Mono.mul t.1.1 t.2.1 = m then t.1.2 * t.2.2 else 0)
          0 =
        keyPairs.foldl
          (fun acc ab =>
            acc + if Mono.mul ab.1 ab.2 = m then
              coeff ab.1 p * coeff ab.2 q
            else 0)
          0 := by
    unfold keyPairs
    rw [List.foldl_map]
    apply List.foldl_congr
    intro acc t ht
    rcases List.mem_flatMap.mp ht with ⟨pt, hpt, ht⟩
    rcases List.mem_map.mp ht with ⟨qt, hqt, rfl⟩
    rw [coeff_eq_of_mem_terms p hpt, coeff_eq_of_mem_terms q hqt]
  have hkeyPairs :
      keyPairs =
        p.monomials.flatMap fun a => q.monomials.map fun b => (a, b) := by
    have cross (xs ys : List (Mono n × R)) :
        (xs.flatMap fun x => ys.map fun y => (x, y)).map
            (fun t => (t.1.1, t.2.1)) =
          (xs.map Prod.fst).flatMap fun x =>
            (ys.map Prod.fst).map fun y => (x, y) := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
          simp only [List.flatMap_cons, List.map_append, List.map_cons, ih,
            List.map_map]
          rfl
    unfold keyPairs pairs monomials
    exact cross p.termsList q.termsList
  have hkeyPairsNodup : keyPairs.Nodup := by
    rw [hkeyPairs]
    unfold List.Nodup
    rw [List.pairwise_flatMap]
    constructor
    · intro a ha
      apply q.monomials_nodup.map (fun b => (a, b))
      intro b c hbc hpair
      exact hbc (congrArg Prod.snd hpair)
    · apply p.monomials_nodup.imp
      intro a c hac x hx y hy hpair
      rcases List.mem_map.mp hx with ⟨b, hb, rfl⟩
      rcases List.mem_map.mp hy with ⟨d, hd, rfl⟩
      exact hac (congrArg Prod.fst hpair)
  have mem_keyPairs (a b : Mono n) :
      (a, b) ∈ keyPairs ↔ a ∈ p.monomials ∧ b ∈ q.monomials := by
    rw [hkeyPairs]
    simp
  let active :=
    keyPairs.filter fun ab => Mono.mul ab.1 ab.2 = m
  let splitActive :=
    (Mono.splits m).filter fun ab =>
      ab.1 ∈ p.monomials ∧ ab.2 ∈ q.monomials
  have hactivePerm : active.Perm splitActive := by
    rw [List.perm_ext_iff_of_nodup
      (hkeyPairsNodup.filter _)
      ((Mono.splits_nodup m).filter _)]
    intro ab
    simp only [List.mem_filter, decide_eq_true_eq]
    rw [mem_keyPairs, Mono.splits_mem_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩, hmul⟩
      exact ⟨hmul, ha, hb⟩
    · rintro ⟨hmul, ha, hb⟩
      exact ⟨⟨ha, hb⟩, hmul⟩
  let value (ab : Mono n × Mono n) :=
    coeff ab.1 p * coeff ab.2 q
  have hkeyFilter :
      keyPairs.foldl
          (fun acc ab =>
            acc + if Mono.mul ab.1 ab.2 = m then value ab else 0)
          0 =
        active.foldl (fun acc ab => acc + value ab) 0 := by
    unfold active
    rw [List.foldl_filter]
    apply List.foldl_congr
    intro acc ab hab
    by_cases hmul : Mono.mul ab.1 ab.2 = m <;>
      simp [hmul, Lean.Grind.AddCommMonoid.add_zero]
  have hsplitFilter :
      splitActive.foldl (fun acc ab => acc + value ab) 0 =
        (Mono.splits m).foldl (fun acc ab => acc + value ab) 0 := by
    unfold splitActive
    rw [List.foldl_filter]
    apply List.foldl_congr
    intro acc ab hab
    unfold value
    by_cases ha : ab.1 ∈ p.monomials
    · by_cases hb : ab.2 ∈ q.monomials
      · simp [ha, hb]
      · rw [coeff_eq_zero_of_not_mem ab.2 q hb,
          Lean.Grind.Semiring.mul_zero, Lean.Grind.AddCommMonoid.add_zero]
        simp [ha, hb]
    · rw [coeff_eq_zero_of_not_mem ab.1 p ha,
        Lean.Grind.Semiring.zero_mul, Lean.Grind.AddCommMonoid.add_zero]
      simp [ha]
  change coeff m (mul p q) = _
  rw [hpairsCoeff, hpairsKeys]
  change
    keyPairs.foldl
        (fun acc ab =>
          acc + if Mono.mul ab.1 ab.2 = m then value ab else 0)
        0 =
      (Mono.splits m).foldl (fun acc ab => acc + value ab) 0
  rw [hkeyFilter, List.foldl_add_perm value hactivePerm 0, hsplitFilter]

/-- Zero is absorbing on the right for polynomial multiplication. -/
theorem mul_zero [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : p * 0 = 0 := by
  apply ext
  intro m
  rw [coeff_mul, coeff_zero]
  simp only [coeff_zero]
  simp only [Lean.Grind.Semiring.mul_zero]
  exact List.foldl_add_zero _ _

/-- Zero is absorbing on the left for polynomial multiplication. -/
theorem zero_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : 0 * p = 0 := by
  apply ext
  intro m
  rw [coeff_mul, coeff_zero]
  simp only [coeff_zero]
  simp only [Lean.Grind.Semiring.zero_mul]
  exact List.foldl_add_zero _ _

/-- Polynomial multiplication distributes over addition on the right. -/
theorem mul_add [Lean.Grind.Semiring R] [DecidableEq R]
    (p q r : MvPoly n R cmp) : p * (q + r) = p * q + p * r := by
  apply ext
  intro m
  simp only [coeff_mul, coeff_add]
  calc
    (Mono.splits m).foldl
        (fun acc ab =>
          acc + coeff ab.1 p * (coeff ab.2 q + coeff ab.2 r)) 0 =
        (Mono.splits m).foldl
          (fun acc ab =>
            acc +
              (coeff ab.1 p * coeff ab.2 q +
                coeff ab.1 p * coeff ab.2 r)) 0 := by
          apply List.foldl_congr
          intro acc ab _
          rw [Lean.Grind.Semiring.left_distrib]
    _ =
        (Mono.splits m).foldl
            (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 +
          (Mono.splits m).foldl
            (fun acc ab => acc + coeff ab.1 p * coeff ab.2 r) 0 :=
      List.foldl_add_add _ _ _

/-- Polynomial multiplication distributes over addition on the left. -/
theorem add_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (p q r : MvPoly n R cmp) : (p + q) * r = p * r + q * r := by
  apply ext
  intro m
  simp only [coeff_mul, coeff_add]
  calc
    (Mono.splits m).foldl
        (fun acc ab =>
          acc + (coeff ab.1 p + coeff ab.1 q) * coeff ab.2 r) 0 =
        (Mono.splits m).foldl
          (fun acc ab =>
            acc +
              (coeff ab.1 p * coeff ab.2 r +
                coeff ab.1 q * coeff ab.2 r)) 0 := by
          apply List.foldl_congr
          intro acc ab _
          rw [Lean.Grind.Semiring.right_distrib]
    _ =
        (Mono.splits m).foldl
            (fun acc ab => acc + coeff ab.1 p * coeff ab.2 r) 0 +
          (Mono.splits m).foldl
            (fun acc ab => acc + coeff ab.1 q * coeff ab.2 r) 0 :=
      List.foldl_add_add _ _ _

/-- Multiplying monomial polynomials multiplies their coefficients and
monomials. -/
theorem monomial_mul_monomial [Lean.Grind.Semiring R] [DecidableEq R]
    (a b : Mono n) (ca cb : R) :
    (monomial a ca : MvPoly n R cmp) * monomial b cb =
      (monomial (Mono.mul a b) (ca * cb) : MvPoly n R cmp) := by
  apply ext
  intro m
  rw [coeff_mul]
  simp only [coeff_monomial]
  by_cases hm : m = Mono.mul a b
  · subst m
    rw [if_pos rfl]
    have hmem : (a, b) ∈ Mono.splits (Mono.mul a b) :=
      (Mono.splits_mem_iff ..).mpr rfl
    calc
      (Mono.splits (Mono.mul a b)).foldl
          (fun acc ab =>
            acc + (if ab.1 = a then ca else 0) *
              if ab.2 = b then cb else 0)
          0 =
          (Mono.splits (Mono.mul a b)).foldl
            (fun acc ab =>
              acc + if ab = (a, b) then ca * cb else 0)
            0 := by
              apply List.foldl_congr
              intro acc ab _
              rcases ab with ⟨x, y⟩
              by_cases hx : x = a
              · subst x
                by_cases hy : y = b
                · subst y
                  simp
                · simp [hy, Lean.Grind.Semiring.mul_zero]
              · simp [hx, Lean.Grind.Semiring.zero_mul]
      _ = 0 + ca * cb :=
        List.foldl_add_single _ _ _ _ hmem (Mono.splits_nodup _)
      _ = ca * cb := by grind
  · rw [if_neg hm]
    apply List.foldl_add_eq_self
    intro ab hab
    have hmul : Mono.mul ab.1 ab.2 = m :=
      (Mono.splits_mem_iff ..).mp hab
    by_cases ha : ab.1 = a
    · by_cases hb : ab.2 = b
      · have hmul' : Mono.mul a b = m := by
          simpa [ha, hb] using hmul
        exact (hm hmul'.symm).elim
      · rw [if_pos ha, if_neg hb, Lean.Grind.Semiring.mul_zero]
    · rw [if_neg ha, Lean.Grind.Semiring.zero_mul]

/-- Binary powering of a monomial polynomial scales its exponent vector. -/
theorem powBySq_monomial [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (c : R) (k : Nat) :
    Mono.powBySq (monomial m c : MvPoly n R cmp) k =
      monomial (Mono.scale k m) (Mono.powBySq c k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero =>
          rw [Mono.powBySq, Mono.powBySq, Mono.zero_scale]
          rfl
      | succ k =>
          have hlt : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
          rw [Mono.powBySq, Mono.powBySq, ih ((k + 1) / 2) hlt,
            monomial_mul_monomial]
          by_cases heven : (k + 1) % 2 = 0
          · rw [if_pos heven, if_pos heven]
            congr 1
            let r := (k + 1) / 2
            change Mono.mul (Mono.scale r m) (Mono.scale r m) =
              Mono.scale (k + 1) m
            have hdecomp := Nat.mod_add_div (k + 1) 2
            have hcount : k + 1 = r + r := by
              simp only [r]
              omega
            apply Vector.ext
            intro i hi
            simp [Mono.mul, Mono.scale, hcount, Nat.add_mul]
          · rw [if_neg heven, if_neg heven, monomial_mul_monomial]
            congr 1
            let r := (k + 1) / 2
            change
              Mono.mul (Mono.mul (Mono.scale r m) (Mono.scale r m)) m =
                Mono.scale (k + 1) m
            have hdecomp := Nat.mod_add_div (k + 1) 2
            have hmod := Nat.mod_two_eq_zero_or_one (k + 1)
            have hcount : k + 1 = (r + r) + 1 := by
              simp only [r]
              omega
            apply Vector.ext
            intro i hi
            simp [Mono.mul, Mono.scale, hcount, Nat.add_mul,
              Nat.succ_mul]

/-- One is a right identity for polynomial multiplication. -/
theorem mul_one [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : p * 1 = p := by
  apply ext
  intro m
  rw [coeff_mul]
  simp only [coeff_one]
  have hmem : (m, Mono.zero) ∈ Mono.splits m :=
    (Mono.splits_mem_iff ..).mpr (Mono.mul_zero m)
  calc
    (Mono.splits m).foldl
        (fun acc ab =>
          acc + coeff ab.1 p *
            if ab.2 = Mono.zero then 1 else 0)
        0 =
        (Mono.splits m).foldl
          (fun acc ab =>
            acc + if ab = (m, Mono.zero) then coeff ab.1 p else 0)
          0 := by
            apply List.foldl_congr
            intro acc ab hab
            have hmul := (Mono.splits_mem_iff ..).mp hab
            by_cases hb : ab.2 = Mono.zero
            · have ha : ab.1 = m := by
                rw [hb, Mono.mul_zero] at hmul
                exact hmul
              have hab' : ab = (m, Mono.zero) := Prod.ext ha hb
              rw [if_pos hb, Lean.Grind.Semiring.mul_one,
                if_pos hab', ha]
            · have hab' : ab ≠ (m, Mono.zero) := by
                intro h
                exact hb (congrArg Prod.snd h)
              rw [if_neg hb, Lean.Grind.Semiring.mul_zero, if_neg hab']
    _ = 0 + coeff m p :=
      List.foldl_add_single _ _ _ _ hmem (Mono.splits_nodup _)
    _ = coeff m p := by grind

/-- One is a left identity for polynomial multiplication. -/
theorem one_mul [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : 1 * p = p := by
  apply ext
  intro m
  rw [coeff_mul]
  simp only [coeff_one]
  have hmem : (Mono.zero, m) ∈ Mono.splits m :=
    (Mono.splits_mem_iff ..).mpr (Mono.zero_mul m)
  calc
    (Mono.splits m).foldl
        (fun acc ab =>
          acc + (if ab.1 = Mono.zero then 1 else 0) * coeff ab.2 p)
        0 =
        (Mono.splits m).foldl
          (fun acc ab =>
            acc + if ab = (Mono.zero, m) then coeff ab.2 p else 0)
          0 := by
            apply List.foldl_congr
            intro acc ab hab
            have hmul := (Mono.splits_mem_iff ..).mp hab
            by_cases ha : ab.1 = Mono.zero
            · have hb : ab.2 = m := by
                rw [ha, Mono.zero_mul] at hmul
                exact hmul
              have hab' : ab = (Mono.zero, m) := Prod.ext ha hb
              simp [hab', Lean.Grind.Semiring.one_mul]
            · have hab' : ab ≠ (Mono.zero, m) := by
                intro h
                exact ha (congrArg Prod.fst h)
              rw [if_neg ha, Lean.Grind.Semiring.zero_mul, if_neg hab']
    _ = 0 + coeff m p :=
      List.foldl_add_single _ _ _ _ hmem (Mono.splits_nodup _)
    _ = coeff m p := by grind

/-- A three-factor monomial split. -/
private abbrev MonoTriple (n : Nat) :=
  Mono n × (Mono n × Mono n)

/-- Three-factor splittings associated from the left. -/
private def splitsLeft (m : Mono n) : List (MonoTriple n) :=
  (Mono.splits m).flatMap fun az =>
    (Mono.splits az.1).map fun xy => (xy.1, (xy.2, az.2))

/-- Three-factor splittings associated from the right. -/
private def splitsRight (m : Mono n) : List (MonoTriple n) :=
  (Mono.splits m).flatMap fun xb =>
    (Mono.splits xb.2).map fun yz => (xb.1, (yz.1, yz.2))

/-- Membership in the left-associated split list is characterized by the
recombined product. -/
private theorem mem_splitsLeft (m : Mono n) (t : MonoTriple n) :
    t ∈ splitsLeft m ↔
      Mono.mul (Mono.mul t.1 t.2.1) t.2.2 = m := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨az, haz, ht⟩
    rcases List.mem_map.mp ht with ⟨xy, hxy, rfl⟩
    have houter := (Mono.splits_mem_iff ..).mp haz
    have hinner := (Mono.splits_mem_iff ..).mp hxy
    rw [hinner, houter]
  · intro ht
    let az : Mono n × Mono n :=
      (Mono.mul t.1 t.2.1, t.2.2)
    have haz : az ∈ Mono.splits m :=
      (Mono.splits_mem_iff ..).mpr ht
    apply List.mem_flatMap.mpr
    refine ⟨az, haz, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(t.1, t.2.1), ?_, rfl⟩
    exact (Mono.splits_mem_iff ..).mpr rfl

/-- Membership in the right-associated split list is characterized by the
recombined product. -/
private theorem mem_splitsRight (m : Mono n) (t : MonoTriple n) :
    t ∈ splitsRight m ↔
      Mono.mul t.1 (Mono.mul t.2.1 t.2.2) = m := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨xb, hxb, ht⟩
    rcases List.mem_map.mp ht with ⟨yz, hyz, rfl⟩
    have houter := (Mono.splits_mem_iff ..).mp hxb
    have hinner := (Mono.splits_mem_iff ..).mp hyz
    rw [hinner, houter]
  · intro ht
    let xb : Mono n × Mono n :=
      (t.1, Mono.mul t.2.1 t.2.2)
    have hxb : xb ∈ Mono.splits m :=
      (Mono.splits_mem_iff ..).mpr ht
    apply List.mem_flatMap.mpr
    refine ⟨xb, hxb, ?_⟩
    apply List.mem_map.mpr
    refine ⟨(t.2.1, t.2.2), ?_, rfl⟩
    exact (Mono.splits_mem_iff ..).mpr rfl

/-- The left-associated splitting list has no duplicate triples. -/
private theorem splitsLeft_nodup (m : Mono n) :
    (splitsLeft m).Nodup := by
  unfold splitsLeft
  apply List.nodup_flatMap_of_disjoint (Mono.splits_nodup m)
  · intro az _
    apply (Mono.splits_nodup az.1).map
    intro xy uv hxy h
    apply hxy
    apply Prod.ext
    · exact congrArg (fun t : MonoTriple n => t.1) h
    · exact congrArg (fun t : MonoTriple n => t.2.1) h
  · intro az _ bz _ hab t hta htb
    have recover (outer : Mono n × Mono n)
        (ht : t ∈
          (Mono.splits outer.1).map fun xy =>
            (xy.1, (xy.2, outer.2))) :
        outer = (Mono.mul t.1 t.2.1, t.2.2) := by
      rcases List.mem_map.mp ht with ⟨xy, hxy, rfl⟩
      apply Prod.ext
      · exact ((Mono.splits_mem_iff ..).mp hxy).symm
      · rfl
    exact hab ((recover az hta).trans (recover bz htb).symm)

/-- The right-associated splitting list has no duplicate triples. -/
private theorem splitsRight_nodup (m : Mono n) :
    (splitsRight m).Nodup := by
  unfold splitsRight
  apply List.nodup_flatMap_of_disjoint (Mono.splits_nodup m)
  · intro xb _
    apply (Mono.splits_nodup xb.2).map
    intro yz uv hyz h
    apply hyz
    apply Prod.ext
    · exact congrArg (fun t : MonoTriple n => t.2.1) h
    · exact congrArg (fun t : MonoTriple n => t.2.2) h
  · intro xb _ yb _ hxb t htx hty
    have recover (outer : Mono n × Mono n)
        (ht : t ∈
          (Mono.splits outer.2).map fun yz =>
            (outer.1, (yz.1, yz.2))) :
        outer = (t.1, Mono.mul t.2.1 t.2.2) := by
      rcases List.mem_map.mp ht with ⟨yz, hyz, rfl⟩
      apply Prod.ext
      · rfl
      · exact ((Mono.splits_mem_iff ..).mp hyz).symm
    exact hxb ((recover xb htx).trans (recover yb hty).symm)

/-- Polynomial multiplication is associative. -/
theorem mul_assoc [Lean.Grind.Semiring R] [DecidableEq R]
    (p q r : MvPoly n R cmp) :
    (p * q) * r = p * (q * r) := by
  apply ext
  intro m
  simp only [coeff_mul]
  let leftValue (t : MonoTriple n) :=
    (coeff t.1 p * coeff t.2.1 q) * coeff t.2.2 r
  let rightValue (t : MonoTriple n) :=
    coeff t.1 p * (coeff t.2.1 q * coeff t.2.2 r)
  have hleft :
      (Mono.splits m).foldl
          (fun acc az =>
            acc +
              (Mono.splits az.1).foldl
                  (fun acc xy =>
                    acc + coeff xy.1 p * coeff xy.2 q)
                  0 *
                coeff az.2 r)
          0 =
        (splitsLeft m).foldl
          (fun acc t => acc + leftValue t) 0 := by
    unfold splitsLeft
    rw [List.foldl_add_flatMap]
    apply List.foldl_congr
    intro acc az _
    symm
    rw [List.foldl_map, List.foldl_add_eq_add_foldl]
    congr 1
    unfold leftValue
    exact List.foldl_add_mul_right_zero
      (Mono.splits az.1)
      (fun xy => coeff xy.1 p * coeff xy.2 q)
      (coeff az.2 r)
  have hright :
      (Mono.splits m).foldl
          (fun acc xb =>
            acc +
              coeff xb.1 p *
                (Mono.splits xb.2).foldl
                  (fun acc yz =>
                    acc + coeff yz.1 q * coeff yz.2 r)
                  0)
          0 =
        (splitsRight m).foldl
          (fun acc t => acc + rightValue t) 0 := by
    unfold splitsRight
    rw [List.foldl_add_flatMap]
    apply List.foldl_congr
    intro acc xb _
    symm
    rw [List.foldl_map, List.foldl_add_eq_add_foldl]
    congr 1
    unfold rightValue
    exact List.foldl_add_mul_left_zero
      (Mono.splits xb.2) (coeff xb.1 p)
      (fun yz => coeff yz.1 q * coeff yz.2 r)
  have hperm : (splitsLeft m).Perm (splitsRight m) :=
    (List.perm_ext_iff_of_nodup
      (splitsLeft_nodup m) (splitsRight_nodup m)).mpr fun t => by
        rw [mem_splitsLeft, mem_splitsRight, Mono.mul_assoc]
  rw [hleft, hright]
  calc
    (splitsLeft m).foldl (fun acc t => acc + leftValue t) 0 =
        (splitsLeft m).foldl (fun acc t => acc + rightValue t) 0 := by
      apply List.foldl_add_congr
      intro t _
      unfold leftValue rightValue
      exact Lean.Grind.Semiring.mul_assoc ..
    _ = (splitsRight m).foldl (fun acc t => acc + rightValue t) 0 :=
      List.foldl_add_perm rightValue hperm 0

/-- Polynomial multiplication is commutative over a commutative
coefficient semiring. -/
theorem mul_comm [Lean.Grind.CommSemiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : p * q = q * p := by
  apply ext
  intro m
  simp only [coeff_mul]
  let swap : Mono n × Mono n → Mono n × Mono n :=
    fun ab => (ab.2, ab.1)
  let swapped := (Mono.splits m).map swap
  have hinj : Function.Injective swap := by
    intro a b h
    apply Prod.ext
    · exact congrArg Prod.snd h
    · exact congrArg Prod.fst h
  have hnodup : swapped.Nodup := by
    unfold swapped
    apply (Mono.splits_nodup m).map
    intro a b hne heq
    exact hne (hinj heq)
  have hperm : (Mono.splits m).Perm swapped := by
    rw [List.perm_ext_iff_of_nodup (Mono.splits_nodup m) hnodup]
    intro ab
    constructor
    · intro hab
      apply List.mem_map.mpr
      refine ⟨swap ab, ?_, ?_⟩
      · apply (Mono.splits_mem_iff ..).mpr
        rw [Mono.mul_comm]
        exact (Mono.splits_mem_iff ..).mp hab
      · simp [swap]
    · intro hab
      rcases List.mem_map.mp hab with ⟨t, ht, rfl⟩
      apply (Mono.splits_mem_iff ..).mpr
      rw [Mono.mul_comm]
      exact (Mono.splits_mem_iff ..).mp ht
  let value (ab : Mono n × Mono n) :=
    coeff ab.1 p * coeff ab.2 q
  calc
    (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 p * coeff ab.2 q) 0 =
        swapped.foldl (fun acc ab => acc + value ab) 0 :=
      List.foldl_add_perm value hperm 0
    _ = (Mono.splits m).foldl
        (fun acc ab => acc + coeff ab.1 q * coeff ab.2 p) 0 := by
      unfold swapped
      rw [List.foldl_map]
      apply List.foldl_congr
      intro acc ab _
      unfold value swap
      rw [Lean.Grind.CommSemiring.mul_comm]

/-- Reference linear recursion for polynomial powers. -/
private def linearPow [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : Nat → MvPoly n R cmp
  | 0 => 1
  | k + 1 => linearPow p k * p

/-- Linear powers turn addition of exponents into multiplication. -/
private theorem linearPow_add [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (a b : Nat) :
    linearPow p (a + b) = linearPow p a * linearPow p b := by
  induction b with
  | zero =>
      rw [Nat.add_zero, linearPow, mul_one]
  | succ b ih =>
      rw [Nat.add_succ, linearPow, ih, linearPow, mul_assoc]

/-- Binary powering agrees with the reference linear recursion. -/
private theorem npowBySq_eq_linearPow
    [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    npowBySq p k = linearPow p k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero =>
          rw [npowBySq, linearPow]
      | succ k =>
          let half := (k + 1) / 2
          have hlt : half < k + 1 := by
            simp only [half]
            exact Nat.div_lt_self (Nat.succ_pos k) (by decide : 1 < 2)
          rw [npowBySq, ih half hlt]
          by_cases heven : (k + 1) % 2 = 0
          · rw [if_pos heven]
            have hdecomp := Nat.mod_add_div (k + 1) 2
            have hcount : k + 1 = half + half := by
              simp only [half]
              omega
            calc
              linearPow p half * linearPow p half =
                  linearPow p (half + half) :=
                (linearPow_add p half half).symm
              _ = linearPow p (k + 1) := by rw [hcount]
          · rw [if_neg heven]
            have hdecomp := Nat.mod_add_div (k + 1) 2
            have hmod := Nat.mod_two_eq_zero_or_one (k + 1)
            have hcount : k + 1 = (half + half) + 1 := by
              simp only [half]
              omega
            calc
              (linearPow p half * linearPow p half) * p =
                  linearPow p (half + half) * p := by
                rw [linearPow_add]
              _ = linearPow p ((half + half) + 1) := rfl
              _ = linearPow p (k + 1) := by rw [hcount]

/-- Polynomial exponentiation satisfies the successor recurrence. -/
theorem pow_succ [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    p ^ (k + 1) = p ^ k * p := by
  change
    npowBySq p (k + 1) = npowBySq p k * p
  rw [npowBySq_eq_linearPow, npowBySq_eq_linearPow]
  rfl

/-- Coefficients of a successor power are given by multiplication with the
preceding power. -/
theorem coeff_pow_succ [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) (k : Nat) :
    coeff m (p ^ (k + 1)) = coeff m (p ^ k * p) :=
  congrArg (coeff m) (pow_succ p k)

/-- Binary polynomial powering agrees with the public power operation. -/
theorem npowBySq_eq_pow [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    npowBySq p k = p ^ k := by
  rfl

end Hex.MvPoly
