/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeQuery

public section

namespace Hex.Endpoint
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute finite endpoint values while retaining both infinities. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ) :
    Endpoint (RationalFn F) → Endpoint ℝ
  | .negInf => .negInf
  | .finite a => .finite (evalMapped embedding a t)
  | .posInf => .posInf

/-- Finite data for an endpoint sign: its value and polynomial evaluation,
or the leading coefficient for either infinite endpoint. -/
@[expose] noncomputable def fractions (a : Endpoint (RationalFn F))
    (p : DensePoly (RationalFn F)) : Finset (RationalFn F) := by
  classical
  exact match a with
  | .finite x => {x, p.eval x}
  | _ => {p.leadingCoeff}

/-- Finite endpoint order uses the two values and their actual difference. -/
@[expose] noncomputable def orderFractions (a b : Endpoint (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact match a, b with
  | .finite x, .finite y => {x, y, x - y}
  | _, _ => ∅

/-- Preserve finite/infinite endpoint signs from the finite recorded data. -/
theorem signAt_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (a : Endpoint (RationalFn F))
    (p : DensePoly (RationalFn F))
    (regular : ∀ i < p.size, Regular embedding t (p.coeff i))
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0)
    (data : ∀ x ∈ a.fractions p, Regular embedding t x ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    (a.specialize embedding t).signAt (fun x : ℝ => (SignType.sign x : Int))
      (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int))) (polynomial embedding p t) =
      a.signAt sign (EndpointSigns.ofSign sign) p := by
  classical
  cases a with
  | negInf =>
    simp only [specialize, signAt, polynomial_leading embedding p t reflects,
      polynomial_degree embedding p t reflects]
    rw [(data p.leadingCoeff (by simp [fractions])).2]
  | posInf =>
    simp only [specialize, signAt, polynomial_leading embedding p t reflects]
    exact (data p.leadingCoeff (by simp [fractions])).2
  | finite x =>
    simp only [specialize, signAt, EndpointSigns.ofSign]
    rw [← polynomial_eval embedding t p x (data x (by simp [fractions])).1 regular]
    exact (data (p.eval x) (by simp [fractions])).2

/-- Preserve endpoint ordering from the finite comparison obligations. -/
theorem lt_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (a b : Endpoint (RationalFn F))
    (data : ∀ x ∈ orderFractions a b, Regular embedding t x ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    (a.specialize embedding t).lt (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int)))
      (b.specialize embedding t) = a.lt (EndpointSigns.ofSign sign) b := by
  classical
  cases a <;> cases b <;> simp only [specialize, lt, EndpointSigns.ofSign]
  rename_i x y
  apply congrArg (fun z : Int => decide (z < 0))
  calc
    (SignType.sign (evalMapped embedding x t - evalMapped embedding y t) : Int) =
        (SignType.sign (evalMapped embedding (x - y) t) : Int) :=
      congrArg (fun z : ℝ => (SignType.sign z : Int))
        (evalMapped_sub embedding x y t
          (data x (by simp [orderFractions])).1
          (data y (by simp [orderFractions])).1).symm
    _ = sign (x - y) := (data (x - y) (by simp [orderFractions])).2

/-- Endpoint nonroot guards are retained by the same finite sign data. -/
theorem nonvanishing_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (a : Endpoint (RationalFn F))
    (p : DensePoly (RationalFn F))
    (regular : ∀ i < p.size, Regular embedding t (p.coeff i))
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0)
    (data : ∀ x ∈ a.fractions p, Regular embedding t x ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    (a.specialize embedding t).nonvanishing
      (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int))) (polynomial embedding p t) =
      a.nonvanishing (EndpointSigns.ofSign sign) p := by
  classical
  cases a with
  | negInf => rfl
  | posInf => rfl
  | finite x =>
    exact congrArg (fun z : Int => z != 0)
      (signAt_specialize embedding t sign (.finite x) p regular reflects data)

end Hex.Endpoint

namespace Hex.TarskiCertificate
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u}

/-- Substitute all actual literal data, keeping context bindings, sign arrays,
variations and the integer query value. No root or chain producer runs. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx) :
    TarskiCertificate ℝ ℝ Ctx := by
  classical
  exact {
    context := cert.context
    head := polynomial embedding cert.head t
    queryPoly := polynomial embedding cert.queryPoly t
    lower := cert.lower.specialize embedding t
    upper := cert.upper.specialize embedding t
    squarefree := cert.squarefree.specialize embedding t
    remainders := cert.remainders.specialize embedding t
    lowerSigns := cert.lowerSigns
    upperSigns := cert.upperSigns
    lowerVariations := cert.lowerVariations
    upperVariations := cert.upperVariations
    value := cert.value }

/-- Finite scalar data for the actual two chain replays, coefficients, endpoint
order/nonroot checks and every finite/infinite endpoint sign in the query. -/
@[expose] noncomputable def fractions
    (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (p f : DensePoly (RationalFn F)) (a b : Endpoint (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact cert.squarefree.fractions ∪ cert.remainders.fractions ∪
    (p.toArray.toList ++ f.toArray.toList ++ (1 : DensePoly (RationalFn F)).toArray.toList).toFinset ∪
    Endpoint.orderFractions a b ∪ a.fractions p ∪ b.fractions p ∪
    (cert.remainders.chain.toList.flatMap (fun r => (a.fractions r ∪ b.fractions r).toList)).toFinset

/-- Replay the complete accepted certificate after finite guarded substitution.
All stored signs, variations and the query value are retained literally. -/
theorem check_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx)
    (p f : DensePoly (RationalFn F)) (a b : Endpoint (RationalFn F)) (value : Int)
    (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (data : ∀ x ∈ cert.fractions p f a b,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : check sign (EndpointSigns.ofSign sign) context p f a b value cert = true) :
    check (fun x : ℝ => (SignType.sign x : Int))
      (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int))) context
      (polynomial embedding p t) (polynomial embedding f t)
      (a.specialize embedding t) (b.specialize embedding t) value
      (cert.specialize embedding t) = true := by
  classical
  have square_data x (hx : x ∈ cert.squarefree.fractions ∪
      (p.toArray.toList ++ (1 : DensePoly (RationalFn F)).toArray.toList).toFinset) :=
    data x (by
      simp only [fractions, Finset.mem_union, List.mem_toFinset, List.mem_append] at hx ⊢
      tauto)
  have remainder_data x (hx : x ∈ cert.remainders.fractions ∪
      (p.toArray.toList ++ f.toArray.toList).toFinset) := data x (by
    simp only [fractions, Finset.mem_union, List.mem_toFinset, List.mem_append] at hx ⊢
    tauto)
  have p_data i (hi : i < p.size) := data (p.coeff i) (by
    have hc := coefficient_mem p i hi
    simp only [fractions, Finset.mem_union, List.mem_toFinset, List.mem_append]
    tauto)
  have endpoint_data e (he : e = a ∨ e = b) r
      (hr : r = p ∨ r ∈ cert.remainders.chain.toList) x (hx : x ∈ e.fractions r) :=
    data x (by
      rcases hr with rfl | hr
      · rcases he with rfl | rfl <;>
          simp only [fractions, Finset.mem_union] <;> tauto
      · have hm : x ∈ (cert.remainders.chain.toList.flatMap
            (fun r => (a.fractions r ∪ b.fractions r).toList)).toFinset := by
          apply List.mem_toFinset.mpr
          apply List.mem_flatMap.mpr
          refine ⟨r, hr, Finset.mem_toList.mpr ?_⟩
          rcases he with rfl | rfl
          · exact Finset.mem_union_left _ hx
          · exact Finset.mem_union_right _ hx
        simp only [fractions, Finset.mem_union]
        tauto)
  have row_data (chain : SignedRemainderChain (RationalFn F))
      (hc : chain = cert.squarefree ∨ chain = cert.remainders) r
      (hr : r ∈ chain.chain.toList) i (hi : i < r.size) := data (r.coeff i) (by
    have hm : r.coeff i ∈ chain.fractions := by
      simp only [SignedRemainderChain.fractions, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl (List.mem_toFinset.mpr
        (List.mem_flatMap.mpr ⟨r, hr, coefficient_mem r i hi⟩))))
    rcases hc with rfl | rfl <;> simp only [fractions, Finset.mem_union] <;> tauto)
  have map_signs e (he : e = a ∨ e = b) :
      signs (fun x : ℝ => (SignType.sign x : Int))
        (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int)))
        (cert.remainders.specialize embedding t).chain (e.specialize embedding t) =
      signs sign (EndpointSigns.ofSign sign) cert.remainders.chain e := by
    simp only [signs, Hex.Array.map'_eq_map, SignedRemainderChain.specialize, Array.map_map]
    apply Array.ext (by simp)
    intro i hi hj
    simp only [Array.getElem_map]
    have bound : i < cert.remainders.chain.size := by simpa using hi
    have hr : cert.remainders.chain[i] ∈ cert.remainders.chain.toList := by simp
    apply Endpoint.signAt_specialize
    · exact fun j hj => (row_data _ (Or.inr rfl) _ hr j hj).1
    · exact fun j hj => (row_data _ (Or.inr rfl) _ hr j hj).2.1
    · exact fun x hx => ⟨(endpoint_data e he _ (Or.inr hr) x hx).1,
        (endpoint_data e he _ (Or.inr hr) x hx).2.2⟩
  have last_constant : SignedRemainderChain.lastIsConstant
      (cert.squarefree.specialize embedding t) =
      SignedRemainderChain.lastIsConstant cert.squarefree := by
    simp only [SignedRemainderChain.lastIsConstant,
      show (cert.squarefree.specialize embedding t).chain.size = cert.squarefree.chain.size by
        simp [SignedRemainderChain.specialize], SignedRemainderChain.entry_specialize]
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
      (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int)))
      (polynomial embedding p t) (a.specialize embedding t) (b.specialize embedding t) =
      checkEndpoints (EndpointSigns.ofSign sign) p a b := by
    simp only [checkEndpoints, polynomial_isZero embedding p t (fun i hi => (p_data i hi).2.1)]
    rw [Endpoint.lt_specialize embedding t sign a b (fun x hx => by
      have hd := data x (by simp only [fractions, Finset.mem_union]; tauto)
      exact ⟨hd.1, hd.2.2⟩)]
    rw [Endpoint.nonvanishing_specialize embedding t sign a p
      (fun i hi => (p_data i hi).1) (fun i hi => (p_data i hi).2.1)
      (fun x hx => ⟨(endpoint_data a (Or.inl rfl) p (Or.inl rfl) x hx).1,
        (endpoint_data a (Or.inl rfl) p (Or.inl rfl) x hx).2.2⟩)]
    rw [Endpoint.nonvanishing_specialize embedding t sign b p
      (fun i hi => (p_data i hi).1) (fun i hi => (p_data i hi).2.1)
      (fun x hx => ⟨(endpoint_data b (Or.inr rfl) p (Or.inl rfl) x hx).1,
        (endpoint_data b (Or.inr rfl) p (Or.inl rfl) x hx).2.2⟩)]
  simp only [check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at accepted
  obtain ⟨hctx, hp, hf, ha, hb, hv, he, hsf, hc, hr, hls, hus, hbl, hbu, hvl, hvu, hval⟩ := accepted
  have square := SignedRemainderChain.check_specialize embedding t sign p 1 cert.squarefree square_data hsf
  have one : polynomial embedding (1 : DensePoly (RationalFn F)) t = 1 := by
    obtain ⟨P, hp⟩ := polynomial_lift embedding t (1 : DensePoly (RationalFn F))
      (fun i hi => (square_data _ (Finset.mem_union_right _
        (List.mem_toFinset.mpr (List.mem_append.mpr
          (Or.inr (coefficient_mem _ i hi)))))).1)
    apply (HexPolyMathlib.equiv (R := ℝ)).injective
    change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
    rw [polynomial_map embedding t 1 P hp, HexPolyMathlib.toPolynomial_one]
    have lift : P = 1 := by
      apply Polynomial.map_injective (regularRing embedding t).subtype
        Subtype.val_injective
      simpa only [Polynomial.map_one, HexPolyMathlib.toPolynomial_one] using hp
    rw [lift, Polynomial.map_one]
  rw [one] at square
  have rem := SignedRemainderChain.check_specialize embedding t sign p f cert.remainders remainder_data hr
  simp only [check_eq, specialize, hctx, hp, hf, ha, hb, hv, ends, square, rem,
    last_constant, hc, he, map_signs a (Or.inl rfl), map_signs b (Or.inr rfl),
    hls, hus, hvl, hvu, decide_true, Bool.true_and]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, true_and]
  exact ⟨by simpa only [hls] using hbl, by simpa only [hus] using hbu,
    by simpa only [hvl, hls, hvu, hus] using hval⟩

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- One positive neighborhood preserves every check and the value of the
supplied infinitesimal Tarski certificate, using its actual finite data. -/
theorem specialize_near [DecidableEq Ctx] (embedding : F →+* ℝ)
    (ordered : StrictMono embedding) (context : Ctx)
    (p f : DensePoly (RationalFn F)) (a b : Endpoint (RationalFn F)) (value : Int)
    (cert : TarskiCertificate (RationalFn F) (RationalFn F) Ctx)
    (accepted : check (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign)
      (EndpointSigns.ofSign (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign))
      context p f a b value cert = true) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      check (fun x : ℝ => (SignType.sign x : Int))
        (EndpointSigns.ofSign (fun x : ℝ => (SignType.sign x : Int))) context
        (polynomial embedding p t) (polynomial embedding f t)
        (a.specialize embedding t) (b.specialize embedding t) value
        (cert.specialize embedding t) = true := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (cert.fractions p f a b)
  refine ⟨η, positive, fun t ht small => ?_⟩
  apply check_specialize embedding t _ context p f a b value cert _ accepted
  intro x hx
  have preserved := signs t ht small x hx
  exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩

/-- info: 'Hex.TarskiCertificate.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.TarskiCertificate.check_specialize

/-- info: 'Hex.TarskiCertificate.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.TarskiCertificate.specialize_near

end Hex.TarskiCertificate
