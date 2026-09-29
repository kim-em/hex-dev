/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bounds
public import HexRealClosure.BisectionFrontier

public section

namespace Hex.RealClosure.Isolation

variable {E : Type u} [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E]
variable [NatCast E] [Neg E] [Inv E]

/-- A whole-line domain tied to the exact input polynomial and sign operation. -/
structure Whole (sign : E → Int) (p : DensePoly E) where
  private mk ::
  domain : Sturm.PreparedDomain E
  bound : domain.sign = sign ∧ domain.head = p ∧
    domain.lower = .negInf ∧ domain.upper = .posInf

/-- Prepare the shared producer on the whole line. -/
def Whole.prepare? (sign : E → Int) (p : DensePoly E) : Option (Whole sign p) :=
  match h : Sturm.prepare sign p .negInf .posInf with
  | none => none
  | some domain => some ⟨domain, Sturm.prepare_eq_some _ _ _ _ _ h⟩

/-- Whole-line dispatch has exactly the domain of shared preparation. -/
theorem Whole.prepare?_isSome (sign : E → Int) (p : DensePoly E) :
    (Whole.prepare? sign p).isSome = (Sturm.prepare sign p .negInf .posInf).isSome := by
  unfold Whole.prepare?
  split <;> simp_all

/-- The two routes awaiting descriptor completion. The bounded route retains
its accepted original bound and every cell after capped refinement. -/
inductive Route (sign : E → Int) (p : DensePoly E) where
  | bounded (bound : Bounds.Bound sign p) (frontier : Bisection.Frontier sign)
  | whole (domain : Whole sign p)

/-- Apply the fixed finite bound policy. If it rejects every candidate, prepare
whole-line BKR input instead. A successful bound always uses capped refinement;
`complete?` classifies a failed refinement after successful initial preparation
as an internal error. -/
@[expose] def dispatch? (sign : E → Int) (p : DensePoly E) : Option (Route sign p) :=
  match Bounds.find? sign p with
  | none => (Whole.prepare? sign p).map Route.whole
  | some bound => do
    let initial ← Bisection.Frontier.prepare? sign p (-bound.value) bound.value
    let result ← initial.refine?
    return .bounded bound result

/-- A returned bounded route comes from the actual bound search and capped
refinement, with no substituted frontier. -/
theorem dispatch?_bounded {sign : E → Int} {p : DensePoly E}
    {bound : Bounds.Bound sign p} {frontier : Bisection.Frontier sign}
    (accepted : dispatch? sign p = some (.bounded bound frontier)) :
    Bounds.find? sign p = some bound ∧ ∃ initial,
      Bisection.Frontier.prepare? sign p (-bound.value) bound.value = some initial ∧
      initial.refine? = some frontier := by
  unfold dispatch? at accepted
  cases hb : Bounds.find? sign p with
  | none =>
    cases hw : Whole.prepare? sign p <;> simp [hb, hw] at accepted
  | some candidate =>
    cases hp : Bisection.Frontier.prepare? sign p (-candidate.value) candidate.value with
    | none => simp [hb, hp] at accepted
    | some initial =>
      cases hr : initial.refine? with
      | none => simp [hb, hp, hr] at accepted
      | some result =>
        simp [hb, hp, hr] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨rfl, initial, hp, hr⟩

/-- A whole-line route is selected only after every finite bound candidate
fails, and retains the shared producer's actual result. -/
theorem dispatch?_whole {sign : E → Int} {p : DensePoly E} {whole : Whole sign p}
    (accepted : dispatch? sign p = some (.whole whole)) :
    Bounds.find? sign p = none ∧ Whole.prepare? sign p = some whole := by
  unfold dispatch? at accepted
  cases hb : Bounds.find? sign p with
  | none =>
    cases hw : Whole.prepare? sign p with
    | none => simp [hb, hw] at accepted
    | some result =>
      simp [hb, hw] at accepted
      subst result
      exact ⟨rfl, rfl⟩
  | some candidate =>
    cases hp : Bisection.Frontier.prepare? sign p (-candidate.value) candidate.value with
    | none => simp [hb, hp] at accepted
    | some initial =>
      cases hr : initial.refine? <;> simp [hb, hp, hr] at accepted

/-- Checked result of the actual dispatcher for this input, rather than an
arbitrarily supplied finite frontier or whole-line domain. -/
structure Search (sign : E → Int) (p : DensePoly E) where
  private mk ::
  route : Route sign p
  computed : dispatch? sign p = some route

/-- Retain the successful dispatch trace as erased evidence. -/
def search? (sign : E → Int) (p : DensePoly E) : Option (Search sign p) :=
  match h : dispatch? sign p with
  | none => none
  | some route => some ⟨route, h⟩

/-- The checked wrapper adds no domain failure. -/
theorem search?_isSome (sign : E → Int) (p : DensePoly E) :
    (search? sign p).isSome = (dispatch? sign p).isSome := by
  unfold search?
  split <;> simp_all

end Hex.RealClosure.Isolation

/-- info: 'Hex.RealClosure.Isolation.dispatch?_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.dispatch?_bounded
/-- info: 'Hex.RealClosure.Isolation.dispatch?_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Isolation.dispatch?_whole
