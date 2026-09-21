/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRootsMathlib.QueryCompare

public section

namespace HexRealRootsMathlib.Query

open Hex HexPolyMathlib.Interpret Polynomial

/-- Accepted literal replay fixes its value to the endpoint variations of its
supplied remainder chain. This does not invoke a producer or root semantics. -/
theorem check_value {D : Type v} {A : Type w} {Ctx : Type u}
    [Zero D] [DecidableEq D] [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    [DecidableEq A] [DecidableEq Ctx]
    (sign : D → Int) (adapter : EndpointAdapter D A) (context : Ctx)
    (p g : DensePoly D) (a b : Endpoint A) (value : Int) (cert : QueryReplay D A Ctx)
    (h : QueryReplay.check sign adapter context p g a b value cert = true) :
    QueryChain.check sign p g cert.remainders = true ∧
      value = (signVar (QueryReplay.signs sign adapter cert.remainders.chain a).toList : Int) -
        signVar (QueryReplay.signs sign adapter cert.remainders.chain b).toList := by
  simp only [QueryReplay.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, hr, hl, hu, _, _, hvl, hvu, hv⟩ := h
  exact ⟨hr, by simpa only [hvl, hvu, hl, hu] using hv⟩

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

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
    (adapter : EndpointAdapter D A) (adapter' : EndpointAdapter E B)
    (a : A) (b : B) (x : K)
    (hbound : ∀ p, -1 ≤ adapter.evalSign p a ∧ adapter.evalSign p a ≤ 1)
    (hbound' : ∀ p, -1 ≤ adapter'.evalSign p b ∧ adapter'.evalSign p b ≤ 1)
    (hneg : ∀ p, adapter.evalSign p a < 0 ↔ (interpret f hz p).eval x < 0)
    (hneg' : ∀ p, adapter'.evalSign p b < 0 ↔ (interpret j jz p).eval x < 0)
    (hzero : ∀ p, adapter.evalSign p a = 0 ↔ (interpret f hz p).eval x = 0)
    (hzero' : ∀ p, adapter'.evalSign p b = 0 ↔ (interpret j jz p).eval x = 0)
    (chain : Array (DensePoly D)) (chain' : Array (DensePoly E))
    (hsize : chain.size = chain'.size)
    (hscale : ∀ i, ∃ c : K, 0 < c ∧
      interpret j jz (chain'.getD i 0) = C c * interpret f hz (chain.getD i 0)) :
    QueryReplay.signs sign adapter chain (.finite a) =
      QueryReplay.signs sign' adapter' chain' (.finite b) := by
  apply Array.ext
  · simpa only [QueryReplay.signs, Hex.Array.size_map'] using hsize
  · intro i hi hi'
    simp only [QueryReplay.signs, Hex.Array.getElem_map', Endpoint.signAt]
    obtain ⟨c, hc, he⟩ := hscale i
    have heval := congrArg (fun p : Polynomial K => p.eval x) he
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at heval
    have hi₀ : i < chain.size := by simpa only [QueryReplay.signs, Hex.Array.size_map'] using hi
    have hi₁ : i < chain'.size := by simpa only [QueryReplay.signs, Hex.Array.size_map'] using hi'
    rw [← Array.getElem_eq_getD (h := hi₀) 0, ← Array.getElem_eq_getD (h := hi₁) 0] at heval
    exact signs_scale _ _ _ _ c hc heval (hbound _) (hbound' _) (hneg _) (hneg' _) (hzero _) (hzero' _)

end HexRealRootsMathlib.Query
