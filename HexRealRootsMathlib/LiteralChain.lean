/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRootsMathlib.ChainCorrespond

public section

/-!
# Literal generalized Sturm chains

This file packages the algebra used by multiplication-only certificate replayers.
Unlike `Hex.ZPoly.sturmChain`, a literal chain is supplied by the caller. Its
three-term identities and terminal unit prove coprimality backwards through the
chain; a positive derivative identity then supplies the head flanks required by
`Sturm.IsSturmChain`.
-/

open Polynomial

namespace Sturm

/-- A positive three-term Sturm recurrence
`C left * a = quotient * b - C right * c`. -/
@[expose] def ReplayStep (a b c : Polynomial ℝ) : Prop :=
  ∃ (left : ℝ) (quotient : Polynomial ℝ) (right : ℝ),
    0 < left ∧ 0 < right ∧
      Polynomial.C left * a = quotient * b - Polynomial.C right * c

/-- Recurrences for a chain of length at least two, ending in a unit.

The recursive shape is convenient both for a compiled array checker to build and
for the soundness proof to consume: each constructor adds exactly one supplied
three-term identity. -/
inductive Replay : Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ) → Prop where
  | pair {a b : Polynomial ℝ} (last : IsUnit b) : Replay a b []
  | cons {a b c : Polynomial ℝ} {rest : List (Polynomial ℝ)}
      (step : ReplayStep a b c) (tail : Replay b c rest) :
      Replay a b (c :: rest)

namespace Replay

/-- The first two entries of a replay are coprime. -/
theorem first_coprime {a b : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (h : Replay a b rest) : IsCoprime a b := by
  induction h with
  | pair hunit =>
      obtain ⟨u, rfl⟩ := hunit
      exact ⟨0, ↑u⁻¹, by simp⟩
  | cons step tail ih =>
      obtain ⟨left, quotient, right, hleft, hright, hrel⟩ := step
      exact HexRealRootsMathlib.coprime_step_rev
        (ne_of_gt hright) hrel ih

/-- Every consecutive pair in a replay is coprime. -/
theorem pair_coprime {x y : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (h : Replay x y rest) : ∀ (i : ℕ) (a b : Polynomial ℝ),
      (x :: y :: rest)[i]? = some a → (x :: y :: rest)[i + 1]? = some b →
      IsCoprime a b := by
  induction h with
  | pair hunit =>
      intro i a b ha hb
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst a
          simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hb
          subst b
          exact (Replay.pair hunit).first_coprime
      | succ i =>
          simp only [List.getElem?_cons_succ] at ha hb
          cases i <;> simp_all
  | cons step tail ih =>
      intro i a b ha hb
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst a
          simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hb
          subst b
          exact (Replay.cons step tail).first_coprime
      | succ i =>
          simp only [List.getElem?_cons_succ] at ha hb
          simpa [Nat.succ_add] using ih i a b ha hb

/-- Every consecutive triple in a replay has its supplied positive recurrence. -/
theorem triple {x y : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (h : Replay x y rest) : ∀ (i : ℕ) (a b c : Polynomial ℝ),
      (x :: y :: rest)[i]? = some a → (x :: y :: rest)[i + 1]? = some b →
      (x :: y :: rest)[i + 2]? = some c → ReplayStep a b c := by
  induction h with
  | pair hunit =>
      intro i a b c ha hb hc
      cases i <;> simp_all
  | cons step tail ih =>
      intro i a b c ha hb hc
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
          subst a
          simp only [Nat.zero_add, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hb
          subst b
          simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at hc
          subst c
          exact step
      | succ i =>
          simp only [List.getElem?_cons_succ] at ha hb hc
          simpa [Nat.succ_add] using ih i a b c ha hb hc

/-- The last entry of a replay is a unit. -/
theorem last_unit {x y : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (h : Replay x y rest) : ∀ q, (x :: y :: rest).getLast? = some q → IsUnit q := by
  induction h with
  | pair hunit =>
      intro q hq
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hq
      subst q
      exact hunit
  | cons step tail ih =>
      intro q hq
      apply ih q
      simpa using hq

end Replay

/-- A literal positive recurrence replay gives all generalized Sturm-chain
axioms. Nonvanishing is kept explicit because a unit terminal and recurrence
identities alone permit a zero entry immediately before a unit. -/
theorem isChain_of_replay {f s₁ : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (hrep : Replay f s₁ rest)
    (hnz : ∀ q ∈ f :: s₁ :: rest, q ≠ 0)
    (δ : ℝ) (hδ : 0 < δ)
    (hderiv : Polynomial.derivative f = Polynomial.C δ * s₁) :
    IsSturmChain f (f :: s₁ :: rest) := by
  have hcop : IsCoprime f s₁ := hrep.first_coprime
  refine { nonempty := by simp, head := rfl, root_flank := ?_, nonzero_mem := hnz,
           consec_coprime := ?_, interior_alternates := ?_, last_no_root := ?_ }
  · intro r hr
    have hs₁r : s₁.eval r ≠ 0 :=
      HexRealRootsMathlib.eval_ne_zero_of_isCoprime hcop hr
    obtain ⟨hleft, hright⟩ :=
      HexRealRootsMathlib.flank_of_key hδ hderiv hr hs₁r
    exact ⟨s₁, rfl, hs₁r, hleft, hright⟩
  · intro i x a b ha hb hax
    exact HexRealRootsMathlib.eval_ne_zero_of_isCoprime
      (hrep.pair_coprime i a b ha hb) hax
  · intro i x a b c ha hb hc hbx
    obtain ⟨left, quotient, right, hleft, hright, hrel⟩ :=
      hrep.triple i a b c ha hb hc
    have hcop_ab := hrep.pair_coprime i a b ha hb
    have heval := congrArg (Polynomial.eval x) hrel
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, hbx, mul_zero,
      zero_sub] at heval
    have hax : a.eval x ≠ 0 :=
      HexRealRootsMathlib.eval_ne_zero_of_isCoprime hcop_ab.symm hbx
    have hcx : c.eval x ≠ 0 := by
      intro hcx
      rw [hcx, mul_zero, neg_zero, mul_eq_zero] at heval
      rcases heval with hzero | hzero
      · exact (ne_of_gt hleft) hzero
      · exact hax hzero
    refine ⟨hax, hcx, ?_⟩
    have hsign : left * (a.eval x * c.eval x) =
        -(right * (c.eval x * c.eval x)) := by
      linear_combination c.eval x * heval
    nlinarith [hsign, hleft, hright, mul_self_pos.mpr hcx]
  · intro q hq x
    have hunit := hrep.last_unit q hq
    obtain ⟨u, hu, hCu⟩ := Polynomial.isUnit_iff.mp hunit
    rw [← hCu, Polynomial.eval_C]
    exact hu.ne_zero

/-- A literal positive recurrence replay proves squarefreeness by genuine
polynomial coprimality of the head and its derivative. -/
theorem squarefree_of_replay {f s₁ : Polynomial ℝ} {rest : List (Polynomial ℝ)}
    (hrep : Replay f s₁ rest)
    (δ : ℝ) (hδ : 0 < δ)
    (hderiv : Polynomial.derivative f = Polynomial.C δ * s₁) :
    Squarefree f := by
  have hcop : IsCoprime f s₁ := hrep.first_coprime
  have hsep : f.Separable := by
    rw [Polynomial.separable_def, hderiv]
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u, v * Polynomial.C δ⁻¹, ?_⟩
    have hC : Polynomial.C δ⁻¹ * Polynomial.C δ = (1 : Polynomial ℝ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ (ne_of_gt hδ), Polynomial.C_1]
    calc
      u * f + (v * Polynomial.C δ⁻¹) * (Polynomial.C δ * s₁) =
          u * f + v * (Polynomial.C δ⁻¹ * Polynomial.C δ) * s₁ := by ring
      _ = u * f + v * s₁ := by rw [hC]; simp
      _ = 1 := huv
  exact hsep.squarefree

end Sturm

namespace HexRealRootsMathlib

/-- An integer-polynomial instance of a positive three-term recurrence. -/
@[expose] def ZReplayStep (a b c : Hex.ZPoly) : Prop :=
  ∃ (left : Int) (quotient : Hex.ZPoly) (right : Int),
    0 < left ∧ 0 < right ∧
      Hex.DensePoly.scale left a = quotient * b - Hex.DensePoly.scale right c

/-- A literal integer-polynomial recurrence chain ending in a nonzero
constant. -/
inductive ZReplay : Hex.ZPoly → Hex.ZPoly → List Hex.ZPoly → Prop where
  | pair {a b : Hex.ZPoly} (last : b.size = 1) : ZReplay a b []
  | cons {a b c : Hex.ZPoly} {rest : List Hex.ZPoly}
      (step : ZReplayStep a b c) (tail : ZReplay b c rest) :
      ZReplay a b (c :: rest)

namespace ZReplay

/-- A normalized size-one dense polynomial is a nonzero constant, hence a unit
after casting. The dense-polynomial no-trailing-zero invariant rules out the
otherwise problematic coefficient array `#[0]`. -/
private theorem cast_unit {p : Hex.ZPoly} (hsize : p.size = 1) :
    IsUnit (toPolyℝ p) := by
  have hp0 : p ≠ 0 := by
    intro hp
    subst p
    simp at hsize
  have hcast0 : toPolyℝ p ≠ 0 := fun h => hp0 (toPolyℝ_eq_zero_iff.mp h)
  have hdegree : (toPolyℝ p).natDegree = 0 := by
    rw [natDegree_toPolyℝ,
      Hex.DensePoly.degree?_eq_some_of_pos_size p (by omega), hsize]
    rfl
  rw [Polynomial.isUnit_iff_degree_eq_zero,
    Polynomial.degree_eq_natDegree hcast0, hdegree]
  rfl

/-- Cast a literal integer replay to the abstract real-polynomial replay. -/
theorem toReplay {a b : Hex.ZPoly} {rest : List Hex.ZPoly}
    (h : ZReplay a b rest) :
    Sturm.Replay (toPolyℝ a) (toPolyℝ b) (rest.map toPolyℝ) := by
  induction h with
  | pair hlast =>
      exact Sturm.Replay.pair (cast_unit hlast)
  | cons step tail ih =>
      apply Sturm.Replay.cons
      · obtain ⟨left, quotient, right, hleft, hright, hrel⟩ := step
        refine ⟨(left : ℝ), toPolyℝ quotient, (right : ℝ), ?_, ?_, ?_⟩
        · exact_mod_cast hleft
        · exact_mod_cast hright
        · have hcast := congrArg toPolyℝ hrel
          simpa [toPolyℝ_scale, toPolyℝ_sub, toPolyℝ_mul] using hcast
      · exact ih

end ZReplay

/-- Checked literal integer identities imply a generalized Sturm chain for the
real cast. -/
theorem ZReplay.isChain {f s₁ : Hex.ZPoly} {rest : List Hex.ZPoly}
    (hrep : ZReplay f s₁ rest)
    (hnz : ∀ q ∈ f :: s₁ :: rest, q ≠ 0)
    (δ : Int) (hδ : 0 < δ)
    (hderiv : Hex.DensePoly.derivative f = Hex.DensePoly.scale δ s₁) :
    Sturm.IsSturmChain (toPolyℝ f) ((f :: s₁ :: rest).map toPolyℝ) := by
  have hnz' : ∀ q ∈ (f :: s₁ :: rest).map toPolyℝ, q ≠ 0 := by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact fun h => hnz z hz (toPolyℝ_eq_zero_iff.mp h)
  have hderiv' : Polynomial.derivative (toPolyℝ f) =
      Polynomial.C (δ : ℝ) * toPolyℝ s₁ := by
    have hcast := congrArg toPolyℝ hderiv
    simpa [toPolyℝ_derivative, toPolyℝ_scale] using hcast
  simpa using Sturm.isChain_of_replay hrep.toReplay hnz' (δ : ℝ)
    (by exact_mod_cast hδ) hderiv'

/-- Checked literal integer identities prove squarefreeness of the real cast. -/
theorem ZReplay.squarefree {f s₁ : Hex.ZPoly} {rest : List Hex.ZPoly}
    (hrep : ZReplay f s₁ rest)
    (δ : Int) (hδ : 0 < δ)
    (hderiv : Hex.DensePoly.derivative f = Hex.DensePoly.scale δ s₁) :
    Squarefree (toPolyℝ f) := by
  have hderiv' : Polynomial.derivative (toPolyℝ f) =
      Polynomial.C (δ : ℝ) * toPolyℝ s₁ := by
    have hcast := congrArg toPolyℝ hderiv
    simpa [toPolyℝ_derivative, toPolyℝ_scale] using hcast
  exact Sturm.squarefree_of_replay hrep.toReplay (δ : ℝ)
    (by exact_mod_cast hδ) hderiv'

namespace Literal

/-- Membership in the real half-open interval represented by `I`. -/
@[expose] def InInterval (I : Hex.DyadicInterval) (x : ℝ) : Prop :=
  Dyadic.toReal I.lower < x ∧ x ≤ Dyadic.toReal I.upper

/-- The multiset of real roots of `f` in a half-open dyadic interval. -/
@[expose] noncomputable def rootsIn
    (f : Polynomial ℝ) (I : Hex.DyadicInterval) : Multiset ℝ := by
  classical
  exact f.roots.filter (InInterval I)

end Literal

/-- A literal chain's finite variation drop is the exact number of roots in a
half-open dyadic interval. This reads the supplied chain directly and never
calls the executable chain builder. -/
theorem literalCount_eq_card_roots (p : Hex.ZPoly) (chain : Array Hex.ZPoly)
    (hp : toPolyℝ p ≠ 0) (hsf : Squarefree (toPolyℝ p))
    (hchain : Sturm.IsSturmChain (toPolyℝ p) (chain.toList.map toPolyℝ))
    (I : Hex.DyadicInterval) :
    (Hex.sturmVarAt chain I.lower : Int) - Hex.sturmVarAt chain I.upper =
      (Literal.rootsIn (toPolyℝ p) I).card := by
  classical
  rw [sturmVarAt_eq, sturmVarAt_eq]
  rw [Literal.rootsIn]
  have h := Sturm.sturm_half_open hp hsf hchain (toReal_lt_toReal I.lt)
  rw [h]
  norm_cast
  apply congrArg Multiset.card
  apply Multiset.filter_congr
  intro x _hx
  rfl

/-- A literal chain's variation drop at infinity is the exact total number of
real roots. -/
theorem literalRootCount_eq_card_roots (p : Hex.ZPoly) (chain : Array Hex.ZPoly)
    (hp : toPolyℝ p ≠ 0) (hsf : Squarefree (toPolyℝ p))
    (hchain : Sturm.IsSturmChain (toPolyℝ p) (chain.toList.map toPolyℝ)) :
    (Hex.sturmVarNegInf chain : Int) - Hex.sturmVarPosInf chain =
      (toPolyℝ p).roots.card := by
  rw [sturmVarNegInf_eq, sturmVarPosInf_eq]
  exact Sturm.sturm_line hp hsf hchain

/-- A checked integer replay gives the exact literal count on an interval.

The array consumed by the executable variation reader is the array conversion
of the replay list, so no separate list/array alignment proof is required. -/
theorem ZReplay.count_eq_card_roots {f s₁ : Hex.ZPoly} {rest : List Hex.ZPoly}
    (hrep : ZReplay f s₁ rest)
    (hnz : ∀ q ∈ f :: s₁ :: rest, q ≠ 0)
    (δ : Int) (hδ : 0 < δ)
    (hderiv : Hex.DensePoly.derivative f = Hex.DensePoly.scale δ s₁)
    (I : Hex.DyadicInterval) :
    (Hex.sturmVarAt (f :: s₁ :: rest).toArray I.lower : Int) -
        Hex.sturmVarAt (f :: s₁ :: rest).toArray I.upper =
      (Literal.rootsIn (toPolyℝ f) I).card := by
  apply literalCount_eq_card_roots f (f :: s₁ :: rest).toArray
  · intro hf
    exact hnz f (by simp) (toPolyℝ_eq_zero_iff.mp hf)
  · exact hrep.squarefree δ hδ hderiv
  · simpa using hrep.isChain hnz δ hδ hderiv

/-- A checked integer replay gives the exact total literal root count. -/
theorem ZReplay.total_eq_card_roots {f s₁ : Hex.ZPoly} {rest : List Hex.ZPoly}
    (hrep : ZReplay f s₁ rest)
    (hnz : ∀ q ∈ f :: s₁ :: rest, q ≠ 0)
    (δ : Int) (hδ : 0 < δ)
    (hderiv : Hex.DensePoly.derivative f = Hex.DensePoly.scale δ s₁) :
    (Hex.sturmVarNegInf (f :: s₁ :: rest).toArray : Int) -
        Hex.sturmVarPosInf (f :: s₁ :: rest).toArray =
      (toPolyℝ f).roots.card := by
  apply literalRootCount_eq_card_roots f (f :: s₁ :: rest).toArray
  · intro hf
    exact hnz f (by simp) (toPolyℝ_eq_zero_iff.mp hf)
  · exact hrep.squarefree δ hδ hderiv
  · simpa using hrep.isChain hnz δ hδ hderiv

end HexRealRootsMathlib
