/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.SelectedSigns
public import HexPoly.Lcm

public section

namespace Hex.RealClosure.Algebraic

/-- A selected-root extension bound to the predecessor's actual operations,
sign, literal context and validated descriptor. The cleanliness predicate
belongs to that predecessor; no field laws on representatives are accepted. -/
structure Context (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    [DecidableEq Ctx] (coeffSign : E → Int) (parent : Ctx) where
  private mk ::
  root : SignDet.Descriptor E Ctx coeffSign parent
  cleanCoeff : E → Bool

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Construct from the shared checked descriptor and predecessor cleanliness.
Interpretation and field/order laws are companion conclusions. -/
def Context.adjoin (root : SignDet.Descriptor E Ctx coeffSign parent)
    (cleanCoeff : E → Bool) : Context E Ctx coeffSign parent := ⟨root, cleanCoeff⟩

private theorem Context.root_adjoin_proof
    (root : SignDet.Descriptor E Ctx coeffSign parent) (cleanCoeff : E → Bool) :
    (Context.adjoin root cleanCoeff).root = root := rfl

theorem Context.root_adjoin (root : SignDet.Descriptor E Ctx coeffSign parent)
    (cleanCoeff : E → Bool) : (Context.adjoin root cleanCoeff).root = root :=
  Context.root_adjoin_proof root cleanCoeff

/-- Delegate the scalar query to the actual shared BKR producer. The explicit
internal-error branch is zero; the companion proves it unreachable under a
zero-reflecting predecessor interpretation preserving arithmetic and sign. -/
@[expose] def Context.signPoly (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : Int :=
  match context.root.buildSigns [p] with
  | .ok signs => signs.value
  | .error _ => 0

theorem Context.signPoly_of_success (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (signs : SignDet.SelectedSigns context.root [p])
    (h : context.root.buildSigns [p] = .ok signs) : context.signPoly p = signs.value := by
  simp [signPoly, h]

/-- Compute and retain the exact monic remainder only for a clean definition.
Nonmonic or nonclean definitions keep the original representative. -/
@[expose] def Context.reduce (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : DensePoly E :=
  if hm : context.root.raw.head.leadingCoeff = 1 then
    if context.root.raw.head.toArray.all context.cleanCoeff then
      (DensePoly.divModMonic p context.root.raw.head hm).2
    else p
  else p

theorem Context.reduce_nonmonic (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : context.root.raw.head.leadingCoeff ≠ 1) :
    context.reduce p = p := by simp [reduce, h]

theorem Context.reduce_unclean (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : context.root.raw.head.toArray.all context.cleanCoeff = false) :
    context.reduce p = p := by
  unfold reduce
  split
  · rw [h]
    rfl
  · rfl

/-- A nonzero representative and its cached sign, bound to the whole immutable
context and the exact stored polynomial. Equality of stored forms is structural. -/
structure Nonzero (context : Context E Ctx coeffSign parent) where
  polynomial : DensePoly E
  sign : Int
  checked : context.signPoly polynomial = sign
  nonzero : sign ≠ 0

instance {context : Context E Ctx coeffSign parent} : DecidableEq (Nonzero context) :=
  fun a b => decidable_of_iff (a.polynomial = b.polynomial ∧ a.sign = b.sign)
    ⟨fun h => by cases a; cases b; cases h.1; cases h.2; rfl,
      fun h => ⟨congrArg Nonzero.polynomial h, congrArg Nonzero.sign h⟩⟩

/-- Nominal context ownership and a unique stored zero. Several nonzero stored
polynomials can denote one value; this carrier has no ring or field instance. -/
structure Element (context : Context E Ctx coeffSign parent) where
  private mk ::
  stored : Option (Nonzero context)

namespace Element

variable {context : Context E Ctx coeffSign parent}

@[ext] theorem ext {a b : Element context} (h : a.stored = b.stored) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (Element context) := fun a b =>
  decidable_of_iff (a.stored = b.stored) ⟨ext, congrArg stored⟩

def zero : Element context := ⟨none⟩
instance : Zero (Element context) := ⟨zero⟩

private theorem stored_zero_proof : (0 : Element context).stored = none := rfl
theorem stored_zero : (0 : Element context).stored = none := stored_zero_proof

/-- Reduction is part of this zero test, so packing retains its computed
remainder and caches the one selected-root query result. -/
def ofPoly (p : DensePoly E) : Element context :=
  let kept := context.reduce p
  let s := context.signPoly kept
  if h : s = 0 then ⟨none⟩ else ⟨some ⟨kept, s, rfl, h⟩⟩

private theorem stored_ofPoly_proof (p : DensePoly E) :
    (ofPoly (context := context) p).stored =
      if h : context.signPoly (context.reduce p) = 0 then none
      else some ⟨context.reduce p, context.signPoly (context.reduce p), rfl, h⟩ := by
  by_cases h : context.signPoly (context.reduce p) = 0 <;> simp only [ofPoly, h, ↓reduceDIte]

theorem stored_ofPoly (p : DensePoly E) :
    (ofPoly (context := context) p).stored =
      if h : context.signPoly (context.reduce p) = 0 then none
      else some ⟨context.reduce p, context.signPoly (context.reduce p), rfl, h⟩ :=
  stored_ofPoly_proof p

@[expose] def polynomial (a : Element context) : DensePoly E :=
  match a.stored with
  | none => 0
  | some p => p.polynomial

/-- A denominator-one polynomial whose coefficients are recursively clean. -/
@[expose] def isClean (a : Element context) : Bool :=
  a.polynomial.toArray.all context.cleanCoeff

/-- Explicit inclusion of a coefficient from this extension's predecessor. -/
@[expose] def ofCoeff (a : E) : Element context := ofPoly (DensePoly.C a)

/-- Cached signs avoid querying a stored nonzero polynomial again. -/
@[expose] def sign (a : Element context) : Int :=
  match a.stored with
  | none => 0
  | some p => p.sign

theorem polynomial_zero : (0 : Element context).polynomial = 0 := by
  simp only [polynomial, stored_zero]

theorem sign_zero : (0 : Element context).sign = 0 := by
  simp only [sign, stored_zero]

theorem sign_eq_zero (a : Element context) : a.sign = 0 ↔ a = 0 := by
  constructor
  · intro hs
    cases h : a.stored with
    | none => apply ext; rw [stored_zero]; exact h
    | some p =>
      have hp : p.sign = 0 := by simpa only [sign, h] using hs
      exact False.elim (p.nonzero hp)
  · intro ha
    rw [ha]
    simp [sign, stored_zero]

@[expose] def add (a b : Element context) : Element context := ofPoly (a.polynomial + b.polynomial)
@[expose] def neg (a : Element context) : Element context := ofPoly (0 - a.polynomial)
@[expose] def sub (a b : Element context) : Element context := ofPoly (a.polynomial - b.polynomial)
@[expose] def mul (a b : Element context) : Element context := ofPoly (a.polynomial * b.polynomial)

/-- The actual local gcd and its complementary factor in the definition. -/
@[expose] def inverseFactor (a : Element context) : DensePoly E × DensePoly E :=
  let g := DensePoly.monicize (DensePoly.gcd context.root.raw.head a.polynomial)
  (g, (DensePoly.divMod context.root.raw.head g).1)

/-- Split locally by the actual gcd, divide the defining polynomial by it,
and scale the one-sided Bézout coefficient by its computed constant gcd. -/
@[expose] def inverseCandidate (a : Element context) : DensePoly E :=
  let eg := DensePoly.xgcdLeft a.polynomial a.inverseFactor.2
  DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left

@[expose] def inv (a : Element context) : Element context :=
  match a.stored with
  | none => 0
  | some _ => ofPoly a.inverseCandidate

instance : One (Element context) := ⟨ofPoly 1⟩
instance : Add (Element context) := ⟨add⟩
instance : Neg (Element context) := ⟨neg⟩
instance : Sub (Element context) := ⟨sub⟩
instance : Mul (Element context) := ⟨mul⟩
instance : Inv (Element context) := ⟨inv⟩
instance : Div (Element context) := ⟨fun a b => a * b⁻¹⟩
instance : NatCast (Element context) := ⟨fun n => ofPoly (DensePoly.C n)⟩
instance (n : Nat) : OfNat (Element context) (n + 2) := ⟨NatCast.natCast (n + 2)⟩

@[expose] def equal (a b : Element context) : Bool := decide ((a - b).sign = 0)

@[expose] def compare (a b : Element context) : Ordering :=
  let s := (a - b).sign
  if s < 0 then .lt else if s = 0 then .eq else .gt

@[expose] def inv? (a : Element context) : Option (Element context) :=
  if a = 0 then none else some a⁻¹

theorem inv?_isNone (a : Element context) : a.inv?.isNone = true ↔ a = 0 := by
  simp [inv?]

end Element
end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.sign_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Algebraic.Element.sign_eq_zero
