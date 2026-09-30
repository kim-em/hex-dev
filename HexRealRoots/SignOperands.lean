/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealRoots.Tarski

public section

/-!
Finite coefficient-sign dependencies of the existing literal replay checkers.
Each inventory is conservative: agreement on every listed operand preserves
exactly the Boolean result, for valid or malformed supplied evidence. Polynomial
arithmetic and literal bindings are not replaced by sign comparisons.

These lemmas permit a finite checked cache to replace a globally lawful sign
operation for one replay. They do not assert that a cache with an arbitrary
fallback is a lawful sign operation on the entire coefficient domain.
-/

namespace Hex.SignedRemainderChain

variable {E : Type u} [Zero E] [DecidableEq E]

/-- A finite inventory of the coefficient signs used by literal chain replay.
Zero is a conservative extra operand for the default-step branch of the proof.
The checker itself ranges only over existing step indices. The inventory may include
unused scales; it is independent of the sign function and of acceptance. -/
@[expose] def signOperands (cert : SignedRemainderChain E) : List E :=
  [0, cert.initial.leftScale, cert.initial.rightScale] ++
    cert.steps.toList.flatMap (fun s => [s.leftScale, s.rightScale]) ++
    cert.terminal.toList.map Prod.fst

variable [One E] [Add E] [Sub E] [Mul E]

omit [One E] in
/-- Replay of a recurrence depends only on its two supplied scale signs. -/
theorem checkStep_congr (sign sign' : E → Int) (a b c : DensePoly E)
    (s : RemainderStep E)
    (hl : sign s.leftScale = sign' s.leftScale)
    (hr : sign s.rightScale = sign' s.rightScale) :
    checkStep sign a b c s = checkStep sign' a b c s := by
  simp only [checkStep, hl, hr]

omit [One E] in
/-- Agreement on the finite inventory preserves both acceptance and rejection
of the actual checker, including malformed and truncated supplied chains. -/
theorem check_sign_congr [NatCast E] (sign sign' : E → Int)
    (p f : DensePoly E) (cert : SignedRemainderChain E)
    (h : ∀ x ∈ cert.signOperands, sign x = sign' x) :
    check sign p f cert = check sign' p f cert := by
  have hz := h 0 (by simp [signOperands])
  have hl := h cert.initial.leftScale (by simp [signOperands])
  have hr := h cert.initial.rightScale (by simp [signOperands])
  have hs (s : RemainderStep E) (hm : s ∈ cert.steps.toList) :
      sign s.leftScale = sign' s.leftScale ∧ sign s.rightScale = sign' s.rightScale := by
    constructor
    · apply h
      simp only [signOperands, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨s, hm, by simp⟩))
    · apply h
      simp only [signOperands, List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨s, hm, by simp⟩))
  have hstep (i : Nat) (a b c : DensePoly E) :
      checkStep sign a b c (cert.steps.getD i ⟨0, 0, 0⟩) =
        checkStep sign' a b c (cert.steps.getD i ⟨0, 0, 0⟩) := by
    rw [Array.getD_eq_getD_getElem?]
    cases hi : cert.steps[i]? with
    | none => simp only [Option.getD_none]; exact checkStep_congr sign sign' a b c _ hz hz
    | some s =>
      simp only [Option.getD_some]
      have hm : s ∈ cert.steps.toList := by simpa using Array.mem_of_getElem? hi
      exact checkStep_congr sign sign' a b c s (hs s hm).1 (hs s hm).2
  simp only [check, hl, hr, hstep]
  cases ht : cert.terminal with
  | none => rfl
  | some t =>
    have hf := h t.1 (by simp [signOperands, ht])
    simp only [hf]

end Hex.SignedRemainderChain

namespace Hex

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [Add E] [Sub E] [Mul E]

namespace Endpoint

omit [Sub E] in
/-- The coefficient passed to the sign operation at this endpoint. -/
@[expose] def signOperand (endpoint : Endpoint E) (p : DensePoly E) : E :=
  match endpoint with
  | .finite a => p.eval a
  | _ => p.leadingCoeff

/-- Only two finite endpoints require a coefficient sign for their order. -/
@[expose] def orderOperands (a b : Endpoint E) : List E :=
  match a, b with
  | .finite a, .finite b => [a - b]
  | _, _ => []

omit [Sub E] in
/-- Only finite endpoints require a polynomial nonvanishing sign. -/
@[expose] def nonvanishingOperands (a : Endpoint E) (p : DensePoly E) : List E :=
  match a with
  | .finite a => [p.eval a]
  | _ => []

/-- Equal operand signs give equal endpoint signs, including both infinities. -/
theorem signAt_congr (sign sign' : E → Int) (a : Endpoint E) (p : DensePoly E)
    (h : sign (a.signOperand p) = sign' (a.signOperand p)) :
    a.signAt sign (EndpointSigns.ofSign sign) p =
      a.signAt sign' (EndpointSigns.ofSign sign') p := by
  cases a <;> simp_all only [signAt, signOperand, EndpointSigns.ofSign]

/-- Endpoint order depends only on the finite difference, when present. -/
theorem lt_congr (sign sign' : E → Int) (a b : Endpoint E)
    (h : ∀ x ∈ orderOperands a b, sign x = sign' x) :
    a.lt (EndpointSigns.ofSign sign) b = a.lt (EndpointSigns.ofSign sign') b := by
  cases a <;> cases b <;> simp_all [lt, orderOperands, EndpointSigns.ofSign] <;> rfl

/-- The nonvanishing guard depends only on its listed finite evaluation. -/
theorem nonvanishing_congr (sign sign' : E → Int) (a : Endpoint E) (p : DensePoly E)
    (h : ∀ x ∈ nonvanishingOperands a p, sign x = sign' x) :
    a.nonvanishing (EndpointSigns.ofSign sign) p =
      a.nonvanishing (EndpointSigns.ofSign sign') p := by
  cases a <;> simp_all [nonvanishing, nonvanishingOperands, EndpointSigns.ofSign]

end Endpoint

namespace TarskiCertificate

/-- All coefficients whose signs can affect this supplied whole query replay.
Repeated operands are retained; sharing belongs to the evidence graph. -/
@[expose] def signOperands (p : DensePoly E) (a b : Endpoint E)
    (cert : TarskiCertificate E E Ctx) : List E :=
  cert.squarefree.signOperands ++ cert.remainders.signOperands ++
    Endpoint.orderOperands a b ++ a.nonvanishingOperands p ++ b.nonvanishingOperands p ++
    cert.remainders.chain.toList.map (a.signOperand ·) ++
    cert.remainders.chain.toList.map (b.signOperand ·)

/-- A literal endpoint sign vector depends only on the listed coefficients. -/
theorem signs_congr (sign sign' : E → Int) (chain : Array (DensePoly E)) (a : Endpoint E)
    (h : ∀ x ∈ chain.toList.map (a.signOperand ·), sign x = sign' x) :
    signs sign (EndpointSigns.ofSign sign) chain a =
      signs sign' (EndpointSigns.ofSign sign') chain a := by
  apply Array.ext (by simp only [signs, Hex.Array.size_map'])
  intro i hi hj
  have hi' : i < chain.size := by simpa only [signs, Hex.Array.size_map'] using hi
  simp only [signs, Hex.Array.getElem_map']
  apply Endpoint.signAt_congr
  apply h
  exact List.mem_map.mpr ⟨chain[i], by simp, rfl⟩

variable [One E] [NatCast E] [DecidableEq Ctx]

/-- Finite sign agreement preserves complete literal query replay, including
all domain guards, endpoint signs, identities and rejection paths, for endpoints
in the coefficient domain with `EndpointSigns.ofSign`. Context and
integer equality and literal binding checks are unchanged. No producer is run. -/
theorem check_sign_congr (sign sign' : E → Int) (context : Ctx)
    (p f : DensePoly E) (a b : Endpoint E) (value : Int)
    (cert : TarskiCertificate E E Ctx)
    (h : ∀ x ∈ signOperands p a b cert, sign x = sign' x) :
    check sign (EndpointSigns.ofSign sign) context p f a b value cert =
      check sign' (EndpointSigns.ofSign sign') context p f a b value cert := by
  have hsf := SignedRemainderChain.check_sign_congr sign sign' p 1 cert.squarefree
    (fun x hx => h x (by simp [signOperands, hx]))
  have hrem := SignedRemainderChain.check_sign_congr sign sign' p f cert.remainders
    (fun x hx => h x (by simp [signOperands, hx]))
  have ho := Endpoint.lt_congr sign sign' a b
    (fun x hx => h x (by simp [signOperands, hx]))
  have ha := Endpoint.nonvanishing_congr sign sign' a p
    (fun x hx => h x (by simp [signOperands, hx]))
  have hb := Endpoint.nonvanishing_congr sign sign' b p
    (fun x hx => h x (by simp [signOperands, hx]))
  have hla := signs_congr sign sign' cert.remainders.chain a
    (fun x hx => h x (by simp [signOperands, hx]))
  have hlb := signs_congr sign sign' cert.remainders.chain b
    (fun x hx => h x (by simp [signOperands, hx]))
  simp only [check, checkDomain, checkQuery, checkEndpoints, hsf, hrem, ho, ha, hb, hla, hlb]

end TarskiCertificate
end Hex
