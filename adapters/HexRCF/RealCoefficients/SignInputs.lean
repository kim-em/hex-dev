/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.LiteralSign
public import HexRCF.RealCoefficients.IsolationCheck
public import HexRCF.Soundness

public section

/-! Collect the finite coefficient signs read by shared Tarski replay. -/

namespace Hex.RCF.RealCoefficients.SignInputs

open Hex

variable {D : Type u} [Zero D] [DecidableEq D]

/-- Scale signs tested by the literal signed-remainder-chain checker. -/
@[expose] def chain (cert : SignedRemainderChain D) : List D :=
  [0, cert.initial.leftScale, cert.initial.rightScale] ++
    cert.steps.toList.flatMap (fun step => [step.leftScale, step.rightScale]) ++
    cert.terminal.toList.map Prod.fst

/-- The coefficient passed to `sign` at one finite or infinite endpoint. -/
@[expose] def endpoint [Add D] [Mul D]
    (q : DensePoly D) (bound : Endpoint D) : List D :=
  match bound with
  | .finite a => [q.eval a]
  | .negInf | .posInf => [q.leadingCoeff]

/-- Inputs read by the endpoint guards for a caller-supplied head and interval. -/
@[expose] def guards [Sub D] [Add D] [Mul D]
    (head : DensePoly D) (lower upper : Endpoint D) : List D :=
  (match lower, upper with
   | .finite a, .finite b => [a - b]
   | _, _ => []) ++
  (match lower with | .finite a => [head.eval a] | _ => []) ++
  (match upper with | .finite b => [head.eval b] | _ => [])

/-- Every sign argument present in a checked Tarski query is reconstructed
from the caller's literal head and endpoints and the supplied chain entries.
The caller may deduplicate this list by exact coordinate equality before
building its finite rational sign table. -/
@[expose] def certificate [Sub D] [Add D] [Mul D] {Ctx : Type v}
    (head : DensePoly D) (lower upper : Endpoint D)
    (cert : TarskiCertificate D D Ctx) : List D :=
  guards head lower upper ++ chain cert.squarefree ++ chain cert.remainders ++
    cert.remainders.chain.toList.flatMap (fun q => endpoint q lower ++ endpoint q upper)

/-- Sign arguments read when an isolation replay checks its total count and
each count-one interval. -/
@[expose] def isolation [One D] [Sub D] [Add D] [Mul D]
    {Ctx : Type v} (point : Dyadic → D) (head : DensePoly D)
    (cert : IsolationReplay D Ctx) : List D :=
  certificate head .negInf .posInf cert.total ++
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      certificate head (.finite (point interval.lower))
        (.finite (point interval.upper)) cert.counts[i]

/-- Sign arguments read by one query on each isolated root. The supplied
query polynomials and certificates must be bound to the same cell indices. -/
@[expose] def rootQueries [Sub D] [Add D] [Mul D]
    {Ctx : Type v} (point : Dyadic → D) (head : DensePoly D)
    (cert : IsolationReplay D Ctx) (queries : List (Fin cert.isolations.intervals.size →
      TarskiCertificate D D Ctx)) : List D :=
  queries.flatMap fun query =>
    (List.finRange cert.isolations.intervals.size).flatMap fun i =>
      let interval := cert.isolations.intervals[i]
      certificate head (.finite (point interval.lower))
        (.finite (point interval.upper)) (query i)

/-- Open-cell sample values used directly by formula evaluation. They are not
part of a Tarski certificate, but the finite field sign table must record them
just as it records signs read while checking certificates. -/
@[expose] def openSamples [Add D] [Mul D] {Ctx : Type v}
    (point : Dyadic → D) (cert : IsolationReplay D Ctx)
    (queries : List (DensePoly D)) : List D :=
  (Cell.all cert.isolations.intervals.size).toList.flatMap fun cell =>
    match cell with
    | .open cut =>
        queries.map fun q => q.eval (point (cert.isolations.openPoint cut))
    | .root _ => []

private theorem chain_step_left (cert : SignedRemainderChain D)
    (step : RemainderStep D) (h : step ∈ cert.steps.toList) :
    step.leftScale ∈ chain cert := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_flatMap.mpr ⟨step, h, by simp⟩))))

private theorem chain_step_right (cert : SignedRemainderChain D)
    (step : RemainderStep D) (h : step ∈ cert.steps.toList) :
    step.rightScale ∈ chain cert := by
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (List.mem_flatMap.mpr ⟨step, h, by simp⟩))))

/-- The signed-remainder replay reads signs only at the listed scales. -/
theorem chain_check_congr [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    (sign₁ sign₂ : D → Int) (p q : DensePoly D) (cert : SignedRemainderChain D)
    (h : ∀ x ∈ chain cert, sign₁ x = sign₂ x) :
    SignedRemainderChain.check sign₁ p q cert =
      SignedRemainderChain.check sign₂ p q cert := by
  have hleft := h cert.initial.leftScale (by simp [chain])
  have hright := h cert.initial.rightScale (by simp [chain])
  have hstep : ∀ i : Nat,
      SignedRemainderChain.checkStep sign₁ (cert.chain.getD i 0)
        (cert.chain.getD (i + 1) 0) (cert.chain.getD (i + 2) 0)
        (cert.steps.getD i ⟨0, 0, 0⟩) =
      SignedRemainderChain.checkStep sign₂ (cert.chain.getD i 0)
        (cert.chain.getD (i + 1) 0) (cert.chain.getD (i + 2) 0)
        (cert.steps.getD i ⟨0, 0, 0⟩) := by
    intro i
    by_cases hi : i < cert.steps.size
    · have hm := Array.getElem_mem_toList (xs := cert.steps) hi
      have hl := h _ (chain_step_left cert cert.steps[i] hm)
      have hr := h _ (chain_step_right cert cert.steps[i] hm)
      simp [Array.getD, hi, SignedRemainderChain.checkStep, hl, hr]
    · have hz := h 0 (by simp [chain])
      simp [Array.getD, hi, SignedRemainderChain.checkStep, hz]
  have hall :
      (Array.range cert.steps.size).all (fun i =>
        SignedRemainderChain.checkStep sign₁ (cert.chain.getD i 0)
          (cert.chain.getD (i + 1) 0) (cert.chain.getD (i + 2) 0)
          (cert.steps.getD i ⟨0, 0, 0⟩)) =
      (Array.range cert.steps.size).all (fun i =>
        SignedRemainderChain.checkStep sign₂ (cert.chain.getD i 0)
          (cert.chain.getD (i + 1) 0) (cert.chain.getD (i + 2) 0)
          (cert.steps.getD i ⟨0, 0, 0⟩)) := by
    exact Array.all_congr rfl hstep rfl rfl
  simp only [SignedRemainderChain.check, hleft, hright, hall]
  split
  · rfl
  · cases ht : cert.terminal with
    | none => simp
    | some pair =>
      obtain ⟨factor, quotient⟩ := pair
      have hf : factor ∈ chain cert := by simp [chain, ht]
      simp [h factor hf]

private theorem endpoint_sign_congr [Sub D] [Add D] [Mul D]
    (sign₁ sign₂ : D → Int) (q : DensePoly D) (bound : Endpoint D)
    (h : ∀ x ∈ endpoint q bound, sign₁ x = sign₂ x) :
    bound.signAt sign₁ (EndpointSigns.ofSign sign₁) q =
      bound.signAt sign₂ (EndpointSigns.ofSign sign₂) q := by
  cases bound with
  | negInf => simp only [endpoint, List.mem_singleton] at h; simp [Endpoint.signAt, h]
  | finite a => simp only [endpoint, List.mem_singleton] at h; simp [Endpoint.signAt, EndpointSigns.ofSign, h]
  | posInf => simp only [endpoint, List.mem_singleton] at h; simp [Endpoint.signAt, h]

/-- Agreement on the reconstructed sign inputs preserves the complete shared
Tarski certificate check, including finite and infinite endpoint guards. -/
theorem certificate_check_congr [One D] [Add D] [Sub D] [Mul D] [NatCast D]
    {Ctx : Type v} [DecidableEq Ctx]
    (sign₁ sign₂ : D → Int) (context : Ctx)
    (head query : DensePoly D) (lower upper : Endpoint D) (value : Int)
    (cert : TarskiCertificate D D Ctx)
    (h : ∀ x ∈ certificate head lower upper cert, sign₁ x = sign₂ x) :
    Sturm.check sign₁ context head query lower upper value cert =
      Sturm.check sign₂ context head query lower upper value cert := by
  have hg (x : D) (hx : x ∈ guards head lower upper) : sign₁ x = sign₂ x :=
    h x (by simp [certificate, hx])
  have hs (x : D) (hx : x ∈ chain cert.squarefree) : sign₁ x = sign₂ x :=
    h x (by simp [certificate, hx])
  have hr (x : D) (hx : x ∈ chain cert.remainders) : sign₁ x = sign₂ x :=
    h x (by simp [certificate, hx])
  have he (q : DensePoly D) (hq : q ∈ cert.remainders.chain.toList)
      (x : D) (hx : x ∈ endpoint q lower ++ endpoint q upper) :
      sign₁ x = sign₂ x :=
    h x (by
      simp only [certificate, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨q, hq, hx⟩))
  have hsf := chain_check_congr sign₁ sign₂ head 1 cert.squarefree hs
  have hrem := chain_check_congr sign₁ sign₂ head query cert.remainders hr
  have hsigns (bound : Endpoint D) (hb : bound = lower ∨ bound = upper) :
      TarskiCertificate.signs sign₁ (EndpointSigns.ofSign sign₁) cert.remainders.chain bound =
      TarskiCertificate.signs sign₂ (EndpointSigns.ofSign sign₂) cert.remainders.chain bound := by
    simp only [TarskiCertificate.signs, Hex.Array.map'_eq_map]
    apply Array.map_congr_left
    intro q hq
    apply endpoint_sign_congr
    intro x hx
    have hq' : q ∈ cert.remainders.chain.toList := by simpa using hq
    rcases hb with rfl | rfl
    · exact he q hq' x (List.mem_append.mpr (Or.inl hx))
    · exact he q hq' x (List.mem_append.mpr (Or.inr hx))
  have hguards :
      TarskiCertificate.checkEndpoints (EndpointSigns.ofSign sign₁) head lower upper =
      TarskiCertificate.checkEndpoints (EndpointSigns.ofSign sign₂) head lower upper := by
    cases lower <;> cases upper
    all_goals simp [TarskiCertificate.checkEndpoints, Endpoint.lt, Endpoint.nonvanishing,
      EndpointSigns.ofSign, guards] at hg ⊢
    all_goals simp_all
    all_goals rfl
  simp only [Sturm.check, TarskiCertificate.check, TarskiCertificate.checkDomain,
    TarskiCertificate.checkQuery, hguards, hsf, hrem, hsigns lower (Or.inl rfl),
    hsigns upper (Or.inr rfl)]

end Hex.RCF.RealCoefficients.SignInputs
