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

/-- Test the cut using native signs and checked exact division. -/
@[expose] def Mode.read? (sign : E → Int) (p : DensePoly E) (point : E) : Option (Mode sign p point) :=
  if h : sign (p.eval point) = 0 then (deflate? p point).map Mode.root
  else some (.regular h)

variable [NatCast E] [Neg E] [Inv E]

/-- Two freshly checked open domains, bound to one active polynomial.
A root cut uses the deflated polynomial on both sides; old evidence is not reused. -/
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

/-- info: 'Hex.RealClosure.Bisection.split?_isSome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bisection.split?_isSome
