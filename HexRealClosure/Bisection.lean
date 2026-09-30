/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Deflation
public import HexSturm

public section

namespace Hex.RealClosure.Bisection

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]

/-- A cut either avoids the original roots or removes its exact linear factor.
Deflation retains the original leading scalar and the computed quotient. -/
inductive Mode (sign : E → Int) (p : DensePoly E) (point : E) where
  | regular (nonroot : sign (p.eval point) ≠ 0)
  | root (deflation : Deflation p point)

@[expose] def Mode.head {sign : E → Int} {p : DensePoly E} {point : E} :
    Mode sign p point → DensePoly E
  | .regular _ => p
  | .root d => d.quotient

/-- The coefficient point emitted by a root cut, or no point for a regular cut. -/
@[expose] def Mode.removed {sign : E → Int} {p : DensePoly E} {point : E} :
    Mode sign p point → Option E
  | .regular _ => none
  | .root _ => some point

/-- A classified cut can emit only its own point. -/
theorem Mode.mem_removed {sign : E → Int} {p : DensePoly E} {point : E}
    (mode : Mode sign p point) (r : E) (h : r ∈ mode.removed) : r = point := by
  cases mode with
  | regular _ => simp [Mode.removed, Option.mem_def] at h
  | root _ => exact (Option.some.inj h).symm

/-- Test the cut using native signs and checked exact division. -/
@[expose] def Mode.read? (sign : E → Int) (p : DensePoly E) (point : E) : Option (Mode sign p point) :=
  if h : sign (p.eval point) = 0 then (deflate? p point).map Mode.root
  else some (.regular h)

variable [NatCast E] [Neg E] [Inv E]

/-- Two open domains with freshly checked endpoints, bound to one active polynomial.
A root cut uses the deflated polynomial on both sides. Regular prepared cuts
may retain the unchanged head's validated derivative chain. -/
structure Split (sign : E → Int) (p : DensePoly E) (lower upper : Endpoint E) (point : E) where
  private mk ::
  mode : Mode sign p point
  left : Sturm.PreparedDomain E
  right : Sturm.PreparedDomain E
  left_bound : left.sign = sign ∧ left.head = mode.head ∧
    left.lower = lower ∧ left.upper = .finite point
  right_bound : right.sign = sign ∧ right.head = mode.head ∧
    right.lower = .finite point ∧ right.upper = upper

/-- Split only at a strictly interior coefficient point. Each side is prepared
against the actual active head, including a fresh derivative-gcd check. -/
def split? (sign : E → Int) (p : DensePoly E) (lower upper : Endpoint E) (point : E) :
    Option (Split sign p lower upper point) :=
  if lower.lt (EndpointSigns.ofSign sign) (.finite point) &&
      (Endpoint.finite point).lt (EndpointSigns.ofSign sign) upper then
    match Mode.read? sign p point with
    | none => none
    | some mode =>
      match hl : Sturm.prepare sign mode.head lower (.finite point) with
      | none => none
      | some left =>
        match hr : Sturm.prepare sign mode.head (.finite point) upper with
        | none => none
        | some right => some ⟨mode, left, right,
            Sturm.prepare_eq_some _ _ _ _ _ hl, Sturm.prepare_eq_some _ _ _ _ _ hr⟩
  else none

/-- Reuse the unchanged head's chain for a regular cut. Deflation changes the
head and therefore prepares its derivative chain afresh. -/
def Mode.prepare? (domain : Sturm.PreparedDomain E) {point : E}
    (mode : Mode domain.sign domain.head point) (lower upper : Endpoint E) :
    Option (Sturm.PreparedDomain E) :=
  match mode with
  | .regular _ => domain.withEndpoints? lower upper
  | .root d => Sturm.prepare domain.sign d.quotient lower upper

/-- Cached preparation returns exactly the same whole domain as fresh work. -/
theorem Mode.prepare?_eq (domain : Sturm.PreparedDomain E) {point : E}
    (mode : Mode domain.sign domain.head point) (lower upper : Endpoint E) :
    mode.prepare? domain lower upper = Sturm.prepare domain.sign mode.head lower upper := by
  cases mode with
  | regular nonroot => exact domain.withEndpoints_eq lower upper
  | root d => rfl

/-- Split an existing validated domain. Regular cuts retain its derivative
chain while checking both new endpoints; root cuts prepare the deflated head. -/
def splitPrepared? (domain : Sturm.PreparedDomain E) (point : E) :
    Option (Split domain.sign domain.head domain.lower domain.upper point) :=
  if domain.lower.lt (EndpointSigns.ofSign domain.sign) (.finite point) &&
      (Endpoint.finite point).lt (EndpointSigns.ofSign domain.sign) domain.upper then
    match Mode.read? domain.sign domain.head point with
    | none => none
    | some mode =>
      match hl : mode.prepare? domain domain.lower (.finite point) with
      | none => none
      | some left =>
        match hr : mode.prepare? domain (.finite point) domain.upper with
        | none => none
        | some right => some ⟨mode, left, right,
            Sturm.prepare_eq_some _ _ _ _ _ ((mode.prepare?_eq _ _ _).symm.trans hl),
            Sturm.prepare_eq_some _ _ _ _ _ ((mode.prepare?_eq _ _ _).symm.trans hr)⟩
  else none

/-- Prepared splitting changes no output, including its mode and whole domains. -/
theorem splitPrepared?_eq (domain : Sturm.PreparedDomain E) (point : E) :
    splitPrepared? domain point =
      split? domain.sign domain.head domain.lower domain.upper point := by
  unfold splitPrepared? split?
  split
  · cases hm : Mode.read? domain.sign domain.head point with
    | none => rfl
    | some mode =>
      repeat' first | rfl | split
      all_goals have hl := mode.prepare?_eq domain domain.lower (.finite point)
      all_goals have hr := mode.prepare?_eq domain (.finite point) domain.upper
      all_goals grind

  · rfl

/-- Success means both actual preparations passed for the classified cut. -/
theorem split?_isSome (sign : E → Int) (p : DensePoly E) (lower upper : Endpoint E) (point : E) :
    (split? sign p lower upper point).isSome = true ↔
      lower.lt (EndpointSigns.ofSign sign) (.finite point) = true ∧
      (Endpoint.finite point).lt (EndpointSigns.ofSign sign) upper = true ∧
      ∃ mode, Mode.read? sign p point = some mode ∧
        (Sturm.prepare sign mode.head lower (.finite point)).isSome = true ∧
        (Sturm.prepare sign mode.head (.finite point) upper).isSome = true := by
  unfold split?
  split
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    cases hc : Mode.read? sign p point with
    | none => simp
    | some mode =>
      cases hl : Sturm.prepare sign mode.head lower (.finite point) with
      | none =>
        simp [hl]
        split <;> simp_all
      | some left =>
        cases hr : Sturm.prepare sign mode.head (.finite point) upper with
        | none =>
          simp [hl, hr]
          split <;> simp_all
          all_goals split <;> simp_all
        | some right =>
          simp [hl, hr, hg.1, hg.2]
          split <;> simp_all
          all_goals split <;> simp_all
  · rename_i hg
    have hn : ¬ (lower.lt (EndpointSigns.ofSign sign) (.finite point) = true ∧
        (Endpoint.finite point).lt (EndpointSigns.ofSign sign) upper = true) := by
      simpa only [Bool.and_eq_true] using hg
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact fun h => hn ⟨h.1, h.2.1⟩

/-- The deterministic finite-interval midpoint uses ordinary native arithmetic. -/
@[expose] def midpoint (lower upper : E) : E := (lower + upper) * (1 + 1)⁻¹

/-- One finite bisection node, including checked removal of a midpoint root. -/
@[expose] def bisect? (sign : E → Int) (p : DensePoly E) (lower upper : E) :
    Option (Split sign p (.finite lower) (.finite upper) (midpoint lower upper)) :=
  split? sign p (.finite lower) (.finite upper) (midpoint lower upper)

end Hex.RealClosure.Bisection

/-- info: 'Hex.RealClosure.Bisection.split?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bisection.split?_isSome

/-- info: 'Hex.RealClosure.Bisection.splitPrepared?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Bisection.splitPrepared?_eq
