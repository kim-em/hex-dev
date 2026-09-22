/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.TarskiCompare

public section

namespace HexRealRootsMathlib.Tarski

open Hex HexPolyMathlib.Interpret Polynomial

/-- Accepted literal replay fixes its value to the endpoint variations of its
supplied remainder chain. This does not invoke a producer or root semantics. -/
theorem check_value {D : Type v} {A : Type w} {Ctx : Type u}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq A] [DecidableEq Ctx]
    (sign : D → Int) (endpointSigns : EndpointSigns D A) (context : Ctx)
    (p g : DensePoly D) (a b : Endpoint A) (value : Int) (cert : TarskiCertificate D A Ctx)
    (h : TarskiCertificate.check sign endpointSigns context p g a b value cert = true) :
    SignedRemainderChain.check sign p g cert.remainders = true ∧
      value = (signVar (TarskiCertificate.signs sign endpointSigns cert.remainders.chain a).toList : Int) -
        signVar (TarskiCertificate.signs sign endpointSigns cert.remainders.chain b).toList := by
  simp only [TarskiCertificate.check_eq, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, hr, hl, hu, _, _, hvl, hvu, hv⟩ := h
  exact ⟨hr, by simpa only [hvl, hvu, hl, hu] using hv⟩


/-- A checked singleton chain has zero variation at both endpoints. -/
theorem check_singleton {D : Type v} {A : Type w} {Ctx : Type u}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq A] [DecidableEq Ctx]
    (sign : D → Int) (endpointSigns : EndpointSigns D A) (context : Ctx)
    (p g : DensePoly D) (a b : Endpoint A) (value : Int) (cert : TarskiCertificate D A Ctx)
    (h : TarskiCertificate.check sign endpointSigns context p g a b value cert = true)
    (hs : cert.remainders.chain.size = 1) : value = 0 := by
  have hv := (check_value sign endpointSigns context p g a b value cert h).2
  have he : cert.remainders.chain = #[cert.remainders.chain[0]'(by omega)] := by
    apply Array.ext
    · simpa using hs
    · intro i hi hj
      have : i = 0 := by simpa using (show i = 0 by omega)
      subst i
      rfl
  rw [he] at hv
  have hz (z : Int) : signVar [z] = 0 := by
    by_cases h : z = 0 <;> simp [signVar, h, signVar.go]
  simpa [TarskiCertificate.signs, Hex.Array.map'_eq_map, hz] using hv

/-- Constant heads force a singleton checked chain, hence a zero answer.
This supported count specialization needs no signed-index theorem. -/
theorem check_constant {D : Type v} {A : Type w} {Ctx : Type u}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq A] [DecidableEq Ctx]
    (sign : D → Int) (endpointSigns : EndpointSigns D A) (context : Ctx)
    (p g : DensePoly D) (a b : Endpoint A) (value : Int) (cert : TarskiCertificate D A Ctx)
    (h : TarskiCertificate.check sign endpointSigns context p g a b value cert = true)
    (hp : p.size = 1) : value = 0 := by
  have hc := (check_value sign endpointSigns context p g a b value cert h).1
  simp only [SignedRemainderChain.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hc
  exact check_singleton sign endpointSigns context p g a b value cert h (by omega)

variable {K : Type u} [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]

omit [DecidableEq K] in
/-- Exact three-valued signs agree when their arguments differ by a positive
factor. Zero evaluations are included. -/
theorem signs_scale (s t : Int) (x y c : K) (hc : 0 < c) (he : y = c * x)
    (hs : -1 ≤ s ∧ s ≤ 1) (ht : -1 ≤ t ∧ t ≤ 1)
    (hsn : s < 0 ↔ x < 0) (htn : t < 0 ↔ y < 0)
    (hsz : s = 0 ↔ x = 0) (htz : t = 0 ↔ y = 0) : s = t := by
  have hn : s < 0 ↔ t < 0 := by
    rw [hsn, htn, he]
    simp only [mul_neg_iff, hc, not_lt_of_gt hc, true_and, false_and, or_false]
  have hz : s = 0 ↔ t = 0 := by rw [hsz, htz, he, mul_eq_zero, or_iff_right (ne_of_gt hc)]
  omega

/-- Positive entrywise scaling preserves the actual finite endpoint sign
arrays, and hence their zero-skipping variation counts. Endpoint carriers and
coefficient representations may differ on the two sides. -/
theorem finite_signs_eq
    {D : Type v} {E : Type w} {A : Type u₁} {B : Type u₂}
    [Zero D] [DecidableEq D] [Zero E] [DecidableEq E]
    (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (j : E → K) (jz : ∀ a, j a = 0 ↔ a = 0)
    (sign : D → Int) (sign' : E → Int)
    (endpointSigns : EndpointSigns D A) (endpointSigns' : EndpointSigns E B)
    (a : A) (b : B) (x : K)
    (hbound : ∀ p, -1 ≤ endpointSigns.evalSign p a ∧ endpointSigns.evalSign p a ≤ 1)
    (hbound' : ∀ p, -1 ≤ endpointSigns'.evalSign p b ∧ endpointSigns'.evalSign p b ≤ 1)
    (hneg : ∀ p, endpointSigns.evalSign p a < 0 ↔ (interpret f hz p).eval x < 0)
    (hneg' : ∀ p, endpointSigns'.evalSign p b < 0 ↔ (interpret j jz p).eval x < 0)
    (hzero : ∀ p, endpointSigns.evalSign p a = 0 ↔ (interpret f hz p).eval x = 0)
    (hzero' : ∀ p, endpointSigns'.evalSign p b = 0 ↔ (interpret j jz p).eval x = 0)
    (chain : Array (DensePoly D)) (chain' : Array (DensePoly E))
    (hsize : chain.size = chain'.size)
    (hscale : ∀ i, ∃ c : K, 0 < c ∧
      interpret j jz (chain'.getD i 0) = C c * interpret f hz (chain.getD i 0)) :
    TarskiCertificate.signs sign endpointSigns chain (.finite a) =
      TarskiCertificate.signs sign' endpointSigns' chain' (.finite b) := by
  apply Array.ext
  · simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hsize
  · intro i hi hi'
    simp only [TarskiCertificate.signs, Hex.Array.getElem_map', Endpoint.signAt]
    obtain ⟨c, hc, he⟩ := hscale i
    have heval := congrArg (fun p : Polynomial K => p.eval x) he
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
    have hi₀ : i < chain.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi
    have hi₁ : i < chain'.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi'
    rw [← Array.getElem_eq_getD (h := hi₀) 0, ← Array.getElem_eq_getD (h := hi₁) 0] at heval
    exact signs_scale _ _ _ _ c hc heval (hbound _) (hbound' _) (hneg _) (hneg' _) (hzero _) (hzero' _)

/-- Positive entrywise scaling preserves signs at both infinities: leading
coefficient signs and degree parity agree, including zero entries. -/
theorem infinite_signs_eq
    {D : Type v} {E : Type w} {A : Type u₁} {B : Type u₂}
    [Zero D] [DecidableEq D] [Zero E] [DecidableEq E]
    (f : D → K) (hz : ∀ a, f a = 0 ↔ a = 0)
    (j : E → K) (jz : ∀ a, j a = 0 ↔ a = 0)
    (sign : D → Int) (sign' : E → Int)
    (endpointSigns : EndpointSigns D A) (endpointSigns' : EndpointSigns E B)
    (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (hbound' : ∀ a, -1 ≤ sign' a ∧ sign' a ≤ 1)
    (hneg : ∀ a, sign a < 0 ↔ f a < 0) (hneg' : ∀ a, sign' a < 0 ↔ j a < 0)
    (hzero : ∀ a, sign a = 0 ↔ f a = 0) (hzero' : ∀ a, sign' a = 0 ↔ j a = 0)
    (chain : Array (DensePoly D)) (chain' : Array (DensePoly E))
    (hsize : chain.size = chain'.size)
    (hscale : ∀ i, ∃ c : K, 0 < c ∧
      interpret j jz (chain'.getD i 0) = C c * interpret f hz (chain.getD i 0)) :
    TarskiCertificate.signs sign endpointSigns chain .negInf =
        TarskiCertificate.signs sign' endpointSigns' chain' .negInf ∧
      TarskiCertificate.signs sign endpointSigns chain .posInf =
        TarskiCertificate.signs sign' endpointSigns' chain' .posInf := by
  have hentries (i : Nat) :
      sign (chain.getD i 0).leadingCoeff = sign' (chain'.getD i 0).leadingCoeff ∧
        (chain.getD i 0).natDegree = (chain'.getD i 0).natDegree := by
    obtain ⟨c, hc, he⟩ := hscale i
    have hl := congrArg Polynomial.leadingCoeff he
    simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, leadingCoeff_interpret] at hl
    constructor
    · exact signs_scale _ _ _ _ c hc hl (hbound _) (hbound' _) (hneg _) (hneg' _) (hzero _) (hzero' _)
    · rw [← natDegree_interpret f hz, ← natDegree_interpret j jz, he,
        Polynomial.natDegree_C_mul (ne_of_gt hc)]
  constructor
  · apply Array.ext
    · simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hsize
    · intro i hi hi'
      have hi₀ : i < chain.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi
      have hi₁ : i < chain'.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi'
      have he := hentries i
      rw [← Array.getElem_eq_getD (h := hi₀) 0, ← Array.getElem_eq_getD (h := hi₁) 0] at he
      simp only [TarskiCertificate.signs, Hex.Array.getElem_map', Endpoint.signAt, he.1, he.2]
  · apply Array.ext
    · simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hsize
    · intro i hi hi'
      have hi₀ : i < chain.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi
      have hi₁ : i < chain'.size := by simpa only [TarskiCertificate.signs, Hex.Array.size_map'] using hi'
      have he := (hentries i).1
      rw [← Array.getElem_eq_getD (h := hi₀) 0, ← Array.getElem_eq_getD (h := hi₁) 0] at he
      simpa only [TarskiCertificate.signs, Hex.Array.getElem_map', Endpoint.signAt] using he

end HexRealRootsMathlib.Tarski
