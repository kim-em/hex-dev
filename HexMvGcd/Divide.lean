/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ExactDiv
public import HexMvGcd.Coeff
public import HexMvPoly.Query

@[expose] public section
set_option backward.proofsInPublic true

/-!
Checked single-divisor reduction for distributed multivariate polynomials.

The loops use the well-founded monomial order, not an arbitrary fuel bound.
Every coefficient quotient is checked by multiplying it back before it can
affect the quotient polynomial.

The SPEC originally omitted `LawfulGcdOps R` from quotient completeness and
decidable divisibility. That assumption is necessary: a bare `GcdOps` may set
`exactDiv` to a junk operation. The executable functions and forward soundness
remain available under bare `GcdOps`; completeness and instances that consume
it require the law package.
-/

namespace Hex.MvPoly

universe u

variable {n : Nat} {R : Type u} {cmp : Mono n → Mono n → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

section Dvd

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]

/-- Polynomial divisibility, with the quotient on the left to agree with the
library's multiplication-facing exact-division convention. -/
instance instDvd : Dvd (MvPoly n R cmp) where
  dvd g f := ∃ q, f = q * g

end Dvd

section Divide

variable [Lean.Grind.CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [Dvd R] [GcdOps R] [IsMonomialOrder cmp]

/-- The leading-monomial relation lifted with `none` as its least element.
This makes zero smaller than every nonzero running dividend. -/
def leadRel (a b : MvPoly n R cmp) : Prop :=
  Option.lt (fun x y => cmp x y = .lt) a.leadingMono b.leadingMono

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Dvd R] [GcdOps R] in
theorem leadRel_wf :
    WellFounded (leadRel (n := n) (R := R) (cmp := cmp)) := by
  apply InvImage.wf (fun p : MvPoly n R cmp => p.leadingMono)
  exact Option.wellFounded_lt IsMonomialOrder.wf

local instance instDivideWf : WellFoundedRelation (MvPoly n R cmp) where
  rel := leadRel
  wf := leadRel_wf

/-- Move the leading term of `r` into the accumulated remainder. -/
def moveLeading (r s : MvPoly n R cmp) (m : Mono n) (c : R) :
    MvPoly n R cmp × MvPoly n R cmp :=
  let t := monomial m c
  (r - t, s + t)

/-- The well-founded division-with-remainder loop. -/
def divModAux (g q r s : MvPoly n R cmp) :
    MvPoly n R cmp × MvPoly n R cmp :=
  match r.leadingTerm with
  | none => (q, s)
  | some (mr, cr) =>
      match g.leadingTerm with
      | none => (q, s + r)
      | some (mg, cg) =>
          match Mono.div mg mr with
          | none =>
              let next := moveLeading r s mr cr
              divModAux g q next.1 next.2
          | some mq =>
              let cq := GcdOps.exactDiv cr cg
              if cq * cg = cr then
                let t := monomial mq cq
                divModAux g (q + t) (r - t * g) s
              else
                let next := moveLeading r s mr cr
                divModAux g q next.1 next.2
termination_by r
decreasing_by
  all_goals sorry

/-- Division with remainder against one divisor. The zero-divisor branch is
fixed as `(0, f)`. -/
def divMod (f g : MvPoly n R cmp) : MvPoly n R cmp × MvPoly n R cmp :=
  if g = 0 then (0, f) else divModAux g 0 f 0

/-- Necessary per-variable degree conditions for exact divisibility. -/
def degreeFilter (f g : MvPoly n R cmp) : Bool :=
  (List.finRange n).all fun i => decide (degreeOf i g ≤ degreeOf i f)

/-- Monomial content, with `none` reserved for the zero polynomial. -/
def monoContent? (f : MvPoly n R cmp) : Option (Mono n) :=
  match f.monomials with
  | [] => none
  | m :: ms => some (ms.foldl Mono.gcd m)

/-- Necessary monomial-content divisibility. -/
def monoFilter (f g : MvPoly n R cmp) : Bool :=
  match monoContent? f, monoContent? g with
  | none, _ => true
  | some _, none => false
  | some mf, some mg => Mono.dvd mg mf

/-- Necessary leading-coefficient divisibility, checked rather than trusted. -/
def coeffFilter (f g : MvPoly n R cmp) : Bool :=
  match f.leadingTerm, g.leadingTerm with
  | none, _ => true
  | some _, none => false
  | some (_, cf), some (_, cg) =>
      GcdOps.exactDiv cf cg * cg == cf

/-- Cheap allocation-free rejection tests ahead of exact trial division. -/
def passesFilter (f g : MvPoly n R cmp) : Bool :=
  degreeFilter f g && monoFilter f g && coeffFilter f g

/-- The fail-fast exact-division loop. Unlike `divModAux`, a term that cannot
be cancelled immediately rejects the candidate. -/
def divExactAux (g q r : MvPoly n R cmp) : Option (MvPoly n R cmp) :=
  match r.leadingTerm with
  | none => some q
  | some (mr, cr) =>
      match g.leadingTerm with
      | none => none
      | some (mg, cg) =>
          match Mono.div mg mr with
          | none => none
          | some mq =>
              let cq := GcdOps.exactDiv cr cg
              if cq * cg = cr then
                let t := monomial mq cq
                divExactAux g (q + t) (r - t * g)
              else
                none
termination_by r
decreasing_by
  all_goals sorry

/-- Exact quotient, rejecting a zero divisor and every failed necessary test
before entering the reduction loop. -/
def divExact? (f g : MvPoly n R cmp) : Option (MvPoly n R cmp) :=
  if g = 0 then
    none
  else if f = 0 then
    some 0
  else if passesFilter f g then
    divExactAux g 0 f
  else
    none

/-- No term of `r` is cancellable by the leading term of `g`. -/
def ReducedBy (r g : MvPoly n R cmp) : Prop :=
  ∀ m c, (m, c) ∈ r.termsList →
    match g.leadingTerm with
    | none => True
    | some (mg, cg) =>
        match Mono.div mg m with
        | none => True
        | some _ => GcdOps.exactDiv c cg * cg ≠ c

/-- Division with remainder reconstructs its dividend. -/
theorem divMod_spec (f g : MvPoly n R cmp) :
    f = (divMod f g).1 * g + (divMod f g).2 := by
  sorry

/-- The returned remainder has no term reducible by the divisor's leading
term. -/
theorem divMod_reduced {f g : MvPoly n R cmp} (hg : g ≠ 0) :
    ReducedBy (divMod f g).2 g := by
  sorry

/-- Exact division rejects a zero right argument. -/
@[simp] theorem divExact?_zero_right (f : MvPoly n R cmp) :
    divExact? f 0 = none := by
  simp [divExact?]

/-- Every quotient returned by the checked loop reconstructs the dividend.
This direction needs no laws for `GcdOps` because each scalar quotient was
validated by multiplication. -/
theorem eq_mul_of_divExact?_eq_some {f g q : MvPoly n R cmp}
    (h : divExact? f g = some q) : f = q * g := by
  sorry

/-- Under lawful coefficient division, the checked exact quotient is complete
as well as sound. -/
theorem divExact?_eq [LawfulGcdOps R] {f g q : MvPoly n R cmp}
    (hg : g ≠ 0) : divExact? f g = some q ↔ f = q * g := by
  sorry

/-- A known nonzero divisor makes the exact-division loop succeed. -/
theorem divExact?_isSome_of_dvd [LawfulGcdOps R] {f g : MvPoly n R cmp}
    (hg : g ≠ 0) : g ∣ f → (divExact? f g).isSome := by
  sorry

/-- Decidable polynomial divisibility. The zero divisor is decided by equality;
the nonzero branch uses checked exact division. -/
instance instDecidableDvd [LawfulGcdOps R] (g f : MvPoly n R cmp) :
    Decidable (g ∣ f) :=
  if hg : g = 0 then
    if hf : f = 0 then
      isTrue (by
        subst g
        subst f
        exact ⟨0, by rw [Lean.Grind.Semiring.zero_mul]⟩)
    else
      isFalse (by
        rintro ⟨q, hq⟩
        rw [hg, Lean.Grind.Semiring.mul_zero] at hq
        exact hf hq)
  else
    match hq : divExact? f g with
    | some q =>
        isTrue ⟨q, (divExact?_eq hg).mp hq⟩
    | none =>
        isFalse fun hd => by
          have hs := divExact?_isSome_of_dvd hg hd
          simp [hq] at hs

/-- Total exact division. Its zero and inexact branches use the stable junk
value zero. -/
instance instDiv : Div (MvPoly n R cmp) where
  div f g := (divExact? f g).getD 0

/-- Total multivariate division cancels every known nonzero exact right
factor. -/
instance instExactDivLaws [LawfulGcdOps R] : ExactDivLaws (MvPoly n R cmp) where
  mul_div_cancel_right := by
    intro a b hb
    change (divExact? (a * b) b).getD 0 = a
    have hq : divExact? (a * b) b = some a :=
      (divExact?_eq hb).mpr rfl
    simp [hq]

end Divide

end Hex.MvPoly
