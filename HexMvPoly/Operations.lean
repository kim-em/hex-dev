/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexBasic.Fold
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

/-- Polynomial addition, combining equal monomials and deleting cancellations. -/
def add [Lean.Grind.Semiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp where
  termsInternal :=
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
            split <;> simp_all

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Add (MvPoly n R cmp) where
  add := add

theorem negCoeff_ne_zero [Lean.Grind.Ring R] (c : R) (hc : c ≠ 0) :
    -c ≠ 0 := by
  grind

/-- Coefficientwise negation. Since negation preserves nonzeroness, this
maps values in place without rebuilding the search tree. -/
def neg [Lean.Grind.Ring R] (p : MvPoly n R cmp) : MvPoly n R cmp :=
  p.mapCoeffs (fun c => -c) negCoeff_ne_zero

instance [Lean.Grind.Ring R] : Neg (MvPoly n R cmp) where
  neg := neg

/-- Polynomial subtraction. -/
def sub [Lean.Grind.Ring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  add p (neg q)

instance [Lean.Grind.Ring R] [DecidableEq R] :
    Sub (MvPoly n R cmp) where
  sub := sub

/-- Polynomial multiplication. Every translated product term is accumulated
directly into one output map, so collisions and cancellations are normalized
as they arise. -/
def mul [Lean.Grind.Semiring R] [DecidableEq R]
    (p q : MvPoly n R cmp) : MvPoly n R cmp :=
  p.foldTerms
    (fun acc mp cp =>
      q.foldTerms
        (fun acc mq cq => acc.addMonomial (Mono.mul mp mq) (cp * cq))
        acc)
    0

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Mul (MvPoly n R cmp) where
  mul := mul

/-- Multiplicative identity. -/
def one [Lean.Grind.Semiring R] [DecidableEq R] : MvPoly n R cmp :=
  C 1

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    One (MvPoly n R cmp) where
  one := one

/-- Exponentiation by repeated squaring. -/
def npowBySq [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) : Nat → MvPoly n R cmp
  | 0 => 1
  | k + 1 =>
      let q := npowBySq p ((k + 1) / 2)
      let q2 := q * q
      if (k + 1) % 2 = 0 then q2 else q2 * p
termination_by k => k
decreasing_by omega

instance [Lean.Grind.Semiring R] [DecidableEq R] :
    Pow (MvPoly n R cmp) Nat where
  pow := npowBySq

@[simp] theorem coeff_one [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) :
    coeff m (1 : MvPoly n R cmp) =
      if m = Mono.zero then 1 else 0 := by
  change coeff m (C 1) = _
  exact coeff_C m 1

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

theorem coeff_neg [Lean.Grind.Ring R] (m : Mono n) (p : MvPoly n R cmp) :
    coeff m (-p) = -coeff m p := by
  change coeff m (neg p) = -coeff m p
  unfold neg mapCoeffs coeff coeff?
  rw [Std.ExtTreeMap.getElem?_map]
  cases p.termsInternal[m]?
  · exact Lean.Grind.AddCommGroup.neg_zero.symm
  · rfl

theorem coeff_sub [Lean.Grind.Ring R] [DecidableEq R]
    (m : Mono n) (p q : MvPoly n R cmp) :
    coeff m (p - q) = coeff m p - coeff m q := by
  change coeff m (p + (-q)) = coeff m p - coeff m q
  rw [coeff_add, coeff_neg, Lean.Grind.Ring.sub_eq_add_neg]

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

theorem coeff_pow_succ [Lean.Grind.Semiring R] [DecidableEq R]
    (m : Mono n) (p : MvPoly n R cmp) (k : Nat) :
    coeff m (p ^ (k + 1)) = coeff m (p ^ k * p) := by
  sorry

theorem npowBySq_eq_pow [Lean.Grind.Semiring R] [DecidableEq R]
    (p : MvPoly n R cmp) (k : Nat) :
    npowBySq p k = p ^ k := by
  rfl

end Hex.MvPoly
