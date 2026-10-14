/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.CoefficientQuery

public section

namespace Hex.Endpoint
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Substitute finite endpoint values while retaining both infinities. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G) :
    Endpoint F → Endpoint G
  | .negInf => .negInf
  | .finite a => .finite (interpretation.map a)
  | .posInf => .posInf

/-- Finite data for an endpoint sign: its value and polynomial evaluation,
or the leading coefficient for either infinite endpoint. -/
@[expose] noncomputable def coefficients (a : Endpoint F)
    (p : DensePoly F) : Finset F := by
  classical
  exact match a with
  | .finite x => {x, p.eval x}
  | _ => {p.leadingCoeff}

/-- Finite endpoint order uses the two values and their actual difference. -/
@[expose] noncomputable def orderCoefficients (a b : Endpoint F) :
    Finset F := by
  classical
  exact match a, b with
  | .finite x, .finite y => {x, y, x - y}
  | _, _ => ∅

/-- Preserve finite/infinite endpoint signs from the finite recorded data. -/
theorem signAt_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (a : Endpoint F)
    (p : DensePoly F)
    (regular : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0)
    (data : ∀ x ∈ a.coefficients p, x ∈ interpretation.domain ∧
      targetSign (interpretation.map x) = sign x) :
    (a.substitute interpretation).signAt targetSign
      (EndpointSigns.ofSign targetSign) (interpretation.polynomial p) =
      a.signAt sign (EndpointSigns.ofSign sign) p := by
  classical
  cases a with
  | negInf =>
    simp only [substitute, signAt, polynomial_leading interpretation p reflects,
      polynomial_degree interpretation p reflects]
    rw [(data p.leadingCoeff (by simp [coefficients])).2]
  | posInf =>
    simp only [substitute, signAt, polynomial_leading interpretation p reflects]
    exact (data p.leadingCoeff (by simp [coefficients])).2
  | finite x =>
    simp only [substitute, signAt, EndpointSigns.ofSign]
    rw [← polynomial_eval interpretation p x (data x (by simp [coefficients])).1 regular]
    exact (data (p.eval x) (by simp [coefficients])).2

/-- Preserve endpoint ordering from the finite comparison obligations. -/
theorem lt_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (a b : Endpoint F)
    (data : ∀ x ∈ orderCoefficients a b, x ∈ interpretation.domain ∧
      targetSign (interpretation.map x) = sign x) :
    (a.substitute interpretation).lt (EndpointSigns.ofSign targetSign)
      (b.substitute interpretation) = a.lt (EndpointSigns.ofSign sign) b := by
  classical
  cases a <;> cases b <;> simp only [substitute, lt, EndpointSigns.ofSign]
  rename_i x y
  apply congrArg (fun z : Int => decide (z < 0))
  rw [← map_sub interpretation (data x (by simp [orderCoefficients])).1
    (data y (by simp [orderCoefficients])).1]
  exact (data (x - y) (by simp [orderCoefficients])).2

/-- Endpoint nonroot guards are retained by the same finite sign data. -/
theorem nonvanishing_map (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (a : Endpoint F)
    (p : DensePoly F)
    (regular : ∀ i < p.size, p.coeff i ∈ interpretation.domain)
    (reflects : ∀ i < p.size, interpretation.map (p.coeff i) = 0 ↔ p.coeff i = 0)
    (data : ∀ x ∈ a.coefficients p, x ∈ interpretation.domain ∧
      targetSign (interpretation.map x) = sign x) :
    (a.substitute interpretation).nonvanishing
      (EndpointSigns.ofSign targetSign) (interpretation.polynomial p) =
      a.nonvanishing (EndpointSigns.ofSign sign) p := by
  classical
  cases a with
  | negInf => rfl
  | posInf => rfl
  | finite x =>
    exact congrArg (fun z : Int => z != 0)
      (signAt_map interpretation sign targetSign (.finite x) p regular reflects data)

end Hex.Endpoint

namespace Hex.TarskiCertificate
open RealClosure.CoefficientMap
attribute [local instance 2000] Field.toGrindField

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G] {Ctx : Type u}

/-- Substitute all actual literal data, keeping context bindings, sign arrays,
variations and the integer query value. No root or chain producer runs. -/
@[expose] noncomputable def substitute (interpretation : RealClosure.CoefficientMap F G)
    (cert : TarskiCertificate F F Ctx) :
    TarskiCertificate G G Ctx := by
  classical
  exact {
    context := cert.context
    head := interpretation.polynomial cert.head
    queryPoly := interpretation.polynomial cert.queryPoly
    lower := cert.lower.substitute interpretation
    upper := cert.upper.substitute interpretation
    squarefree := cert.squarefree.substitute interpretation
    remainders := cert.remainders.substitute interpretation
    lowerSigns := cert.lowerSigns
    upperSigns := cert.upperSigns
    lowerVariations := cert.lowerVariations
    upperVariations := cert.upperVariations
    value := cert.value }

/-- Finite scalar data for the actual two chain replays, coefficients, endpoint
order/nonroot checks and every finite/infinite endpoint sign in the query. -/
@[expose] noncomputable def coefficients
    (cert : TarskiCertificate F F Ctx)
    (p f : DensePoly F) (a b : Endpoint F) :
    Finset F := by
  classical
  exact cert.squarefree.coefficients ∪ cert.remainders.coefficients ∪
    (p.toArray.toList ++ f.toArray.toList ++ (1 : DensePoly F).toArray.toList).toFinset ∪
    Endpoint.orderCoefficients a b ∪ a.coefficients p ∪ b.coefficients p ∪
    (cert.remainders.chain.toList.flatMap (fun r => (a.coefficients r ∪ b.coefficients r).toList)).toFinset

/-- Replay the complete accepted certificate after finite guarded substitution.
All stored signs, variations and the query value are retained literally. -/
theorem check_map [DecidableEq Ctx] (interpretation : RealClosure.CoefficientMap F G)
    (sign : F → Int) (targetSign : G → Int) (context : Ctx)
    (p f : DensePoly F) (a b : Endpoint F) (value : Int)
    (cert : TarskiCertificate F F Ctx)
    (data : ∀ x ∈ cert.coefficients p f a b,
      x ∈ interpretation.domain ∧ (interpretation.map x = 0 ↔ x = 0) ∧
      targetSign (interpretation.map x) = sign x)
    (accepted : check sign (EndpointSigns.ofSign sign) context p f a b value cert = true) :
    check targetSign
      (EndpointSigns.ofSign targetSign) context
      (interpretation.polynomial p) (interpretation.polynomial f)
      (a.substitute interpretation) (b.substitute interpretation) value
      (cert.substitute interpretation) = true := by
  classical
  have square_data x (hx : x ∈ cert.squarefree.coefficients ∪
      (p.toArray.toList ++ (1 : DensePoly F).toArray.toList).toFinset) :=
    data x (by
      simp only [coefficients, Finset.mem_union, List.mem_toFinset, List.mem_append] at hx ⊢
      tauto)
  have remainder_data x (hx : x ∈ cert.remainders.coefficients ∪
      (p.toArray.toList ++ f.toArray.toList).toFinset) := data x (by
    simp only [coefficients, Finset.mem_union, List.mem_toFinset, List.mem_append] at hx ⊢
    tauto)
  have p_data i (hi : i < p.size) := data (p.coeff i) (by
    have hc := coefficient_mem p i hi
    simp only [coefficients, Finset.mem_union, List.mem_toFinset, List.mem_append]
    tauto)
  have endpoint_data e (he : e = a ∨ e = b) r
      (hr : r = p ∨ r ∈ cert.remainders.chain.toList) x (hx : x ∈ e.coefficients r) :=
    data x (by
      rcases hr with rfl | hr
      · rcases he with rfl | rfl <;>
          simp only [coefficients, Finset.mem_union] <;> tauto
      · have hm : x ∈ (cert.remainders.chain.toList.flatMap
            (fun r => (a.coefficients r ∪ b.coefficients r).toList)).toFinset := by
          apply List.mem_toFinset.mpr
          apply List.mem_flatMap.mpr
          refine ⟨r, hr, Finset.mem_toList.mpr ?_⟩
          rcases he with rfl | rfl
          · exact Finset.mem_union_left _ hx
          · exact Finset.mem_union_right _ hx
        simp only [coefficients, Finset.mem_union]
        tauto)
  have row_data (chain : SignedRemainderChain F)
      (hc : chain = cert.squarefree ∨ chain = cert.remainders) r
      (hr : r ∈ chain.chain.toList) i (hi : i < r.size) := data (r.coeff i) (by
    have hm : r.coeff i ∈ chain.coefficients := by
      simp only [SignedRemainderChain.coefficients, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, hr, coefficient_mem r i hi⟩))))
    rcases hc with rfl | rfl <;> simp only [coefficients, Finset.mem_union] <;> tauto)
  have map_signs e (he : e = a ∨ e = b) :
      signs targetSign
        (EndpointSigns.ofSign targetSign)
        (cert.remainders.substitute interpretation).chain (e.substitute interpretation) =
      signs sign (EndpointSigns.ofSign sign) cert.remainders.chain e := by
    simp only [signs, Hex.Array.map'_eq_map, SignedRemainderChain.substitute, Array.map_map]
    apply Array.ext (by simp)
    intro i hi hj
    simp only [Array.getElem_map]
    have bound : i < cert.remainders.chain.size := by simpa using hi
    have hr : cert.remainders.chain[i] ∈ cert.remainders.chain.toList := by simp
    apply Endpoint.signAt_map interpretation sign targetSign
    · exact fun j hj => (row_data _ (Or.inr rfl) _ hr j hj).1
    · exact fun j hj => (row_data _ (Or.inr rfl) _ hr j hj).2.1
    · exact fun x hx => ⟨(endpoint_data e he _ (Or.inr hr) x hx).1,
        (endpoint_data e he _ (Or.inr hr) x hx).2.2⟩
  have last_constant : SignedRemainderChain.lastIsConstant
      (cert.squarefree.substitute interpretation) =
      SignedRemainderChain.lastIsConstant cert.squarefree := by
    simp only [SignedRemainderChain.lastIsConstant,
      show (cert.squarefree.substitute interpretation).chain.size = cert.squarefree.chain.size by
        simp [SignedRemainderChain.substitute], SignedRemainderChain.entry_map]
    congr 1
    apply polynomial_size
    rw [Array.getD_eq_getD_getElem?]
    cases h : cert.squarefree.chain[cert.squarefree.chain.size - 1]? with
    | none => simp only [Option.getD_none]; intro i hi; simp at hi
    | some r =>
      simp only [Option.getD_some]
      exact fun i hi => (row_data _ (Or.inl rfl) r
        (by simpa using Array.mem_of_getElem? h) i hi).2.1
  have ends : checkEndpoints
      (EndpointSigns.ofSign targetSign)
      (interpretation.polynomial p) (a.substitute interpretation) (b.substitute interpretation) =
      checkEndpoints (EndpointSigns.ofSign sign) p a b := by
    simp only [checkEndpoints, polynomial_isZero interpretation p (fun i hi => (p_data i hi).2.1)]
    rw [Endpoint.lt_map interpretation sign targetSign a b (fun x hx => by
      have hd := data x (by simp only [coefficients, Finset.mem_union]; tauto)
      exact ⟨hd.1, hd.2.2⟩)]
    rw [Endpoint.nonvanishing_map interpretation sign targetSign a p
      (fun i hi => (p_data i hi).1) (fun i hi => (p_data i hi).2.1)
      (fun x hx => ⟨(endpoint_data a (Or.inl rfl) p (Or.inl rfl) x hx).1,
        (endpoint_data a (Or.inl rfl) p (Or.inl rfl) x hx).2.2⟩)]
    rw [Endpoint.nonvanishing_map interpretation sign targetSign b p
      (fun i hi => (p_data i hi).1) (fun i hi => (p_data i hi).2.1)
      (fun x hx => ⟨(endpoint_data b (Or.inr rfl) p (Or.inl rfl) x hx).1,
        (endpoint_data b (Or.inr rfl) p (Or.inl rfl) x hx).2.2⟩)]
  simp only [check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  obtain ⟨hctx, hp, hf, ha, hb, hv, he, hsf, hc, hr, hls, hus, hbl, hbu, hvl, hvu, hval⟩ := accepted
  have square := SignedRemainderChain.check_map interpretation sign targetSign p 1 cert.squarefree square_data hsf
  have one : interpretation.polynomial (1 : DensePoly F) = 1 := polynomial_one interpretation
  rw [one] at square
  have rem := SignedRemainderChain.check_map interpretation sign targetSign p f cert.remainders remainder_data hr
  simp only [check_eq, substitute, hctx, hp, hf, ha, hb, hv, ends, square, rem,
    last_constant, hc, he, map_signs a (Or.inl rfl), map_signs b (Or.inr rfl),
    hls, hus, hvl, hvu, decide_true, Bool.true_and]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, true_and]
  exact ⟨by simpa only [hls] using hbl, by simpa only [hus] using hbu,
    by simpa only [hvl, hls, hvu, hus] using hval⟩

/-- A positive first-parameter neighborhood preserves the complete accepted
Tarski query certificate, including endpoint signs and its stored query value. -/
theorem firstMap_near [DecidableEq Ctx] (context : Ctx)
    (p f : DensePoly (RationalFn (RationalFn ℝ)))
    (a b : Endpoint (RationalFn (RationalFn ℝ))) (value : Int)
    (cert : TarskiCertificate (RationalFn (RationalFn ℝ))
      (RationalFn (RationalFn ℝ)) Ctx)
    (accepted : check
      (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign))
      (EndpointSigns.ofSign
        (OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)))
      context p f a b value cert = true) :
    ∀ᶠ first in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      check (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
        (EndpointSigns.ofSign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)) context
        ((RealClosure.Specialize.firstMap first).polynomial p)
        ((RealClosure.Specialize.firstMap first).polynomial f)
        (a.substitute (RealClosure.Specialize.firstMap first))
        (b.substitute (RealClosure.Specialize.firstMap first)) value
        (cert.substitute (RealClosure.Specialize.firstMap first)) = true := by
  filter_upwards [RealClosure.Specialize.firstMap_near (cert.coefficients p f a b)] with first data
  exact check_map (RealClosure.Specialize.firstMap first) _ _ context p f a b value cert data accepted

/-- info: 'Hex.TarskiCertificate.check_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.TarskiCertificate.check_map

/-- info: 'Hex.TarskiCertificate.firstMap_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.TarskiCertificate.firstMap_near

end Hex.TarskiCertificate
