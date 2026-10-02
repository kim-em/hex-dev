/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.QueryHandle
public import HexPoly.Lcm
public import HexPoly.PseudoGcd

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
  handle : Option (SignDet.QueryHandle root)
  handle_checked : handle = root.prepareQueries
  cleanCoeff : E → Bool
  canReduce : Bool
  reduce_checked : canReduce =
    (decide (root.raw.head.leadingCoeff = 1) && root.raw.head.toArray.all cleanCoeff)

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- Construct from the shared checked descriptor and predecessor cleanliness.
Interpretation and field/order laws are companion conclusions. -/
def Context.adjoin (root : SignDet.Descriptor E Ctx coeffSign parent)
    (cleanCoeff : E → Bool) : Context E Ctx coeffSign parent :=
  ⟨root, root.prepareQueries, rfl, cleanCoeff,
    decide (root.raw.head.leadingCoeff = 1) && root.raw.head.toArray.all cleanCoeff, rfl⟩

private theorem Context.root_adjoin_proof
    (root : SignDet.Descriptor E Ctx coeffSign parent) (cleanCoeff : E → Bool) :
    (Context.adjoin root cleanCoeff).root = root := rfl

theorem Context.root_adjoin (root : SignDet.Descriptor E Ctx coeffSign parent)
    (cleanCoeff : E → Bool) : (Context.adjoin root cleanCoeff).root = root :=
  Context.root_adjoin_proof root cleanCoeff

private theorem Context.clean_adjoin_proof
    (root : SignDet.Descriptor E Ctx coeffSign parent) (cleanCoeff : E → Bool) :
    (Context.adjoin root cleanCoeff).cleanCoeff = cleanCoeff := rfl

theorem Context.clean_adjoin (root : SignDet.Descriptor E Ctx coeffSign parent)
    (cleanCoeff : E → Bool) : (Context.adjoin root cleanCoeff).cleanCoeff = cleanCoeff :=
  Context.clean_adjoin_proof root cleanCoeff

/-- Reuse the prepared root domain retained when the context was constructed.
For coefficients outside the companion's lawful interpretation, failed
preparation keeps the original producer and its diagnostic behavior. -/
@[expose] def Context.buildSigns (context : Context E Ctx coeffSign parent)
    (qs : List (DensePoly E)) : Except SignDet.BuildError (SignDet.SelectedSigns context.root qs) :=
  match context.handle with
  | some handle => handle.buildSigns qs
  | none => context.root.buildSigns qs

/-- Domain reuse changes neither the actual certificates nor query failure. -/
theorem Context.buildSigns_eq (context : Context E Ctx coeffSign parent)
    (qs : List (DensePoly E)) : context.buildSigns qs = context.root.buildSigns qs := by
  unfold buildSigns
  split
  · exact SignDet.QueryHandle.buildSigns_eq _ _
  · rfl

/-- Delegate the scalar query to the actual shared BKR producer. The explicit
internal-error branch is zero; the companion proves it unreachable under a
zero-reflecting predecessor interpretation preserving arithmetic and sign. -/
@[expose] def Context.signQuery (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : Int :=
  if p.size ≤ 1 then coeffSign (p.coeff 0)
  else
    match context.buildSigns [p] with
    | .ok signs => signs.value
    | .error _ => 0

theorem Context.signQuery_const (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : p.size ≤ 1) : context.signQuery p = coeffSign (p.coeff 0) := by
  simp only [signQuery, h, ↓reduceIte]

theorem Context.signQuery_of_success (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (signs : SignDet.SelectedSigns context.root [p])
    (h : context.root.buildSigns [p] = .ok signs) (hsize : 1 < p.size) :
    context.signQuery p = signs.value := by
  simp [signQuery, context.buildSigns_eq, h, Nat.not_le_of_gt hsize]

/-- Compute only the sign-corrected pseudo-remainder needed by a scalar query.
The multiplier power and corrected quotient are not used by the query. -/
@[expose] def Context.queryRemainder (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : DensePoly E :=
  let remainder := (DensePoly.pseudoDivMod p context.root.raw.head).2
  if DensePoly.pseudoExponent p context.root.raw.head % 2 = 1 ∧
      coeffSign context.root.raw.head.leadingCoeff < 0 then
    -remainder
  else remainder

/-- The direct query remainder agrees with the shared positive pseudo-division. -/
theorem Context.queryRemainder_eq (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) :
    context.queryRemainder p =
      (DensePoly.positivePseudoDiv coeffSign p context.root.raw.head).remainder := by
  unfold queryRemainder DensePoly.positivePseudoDiv DensePoly.pseudoDiv
  split <;> rfl

/-- Keep constants and already-smaller queries. For larger queries use the
shared positive pseudo-remainder; its positive scalar preserves the sign at
this root. Stored representatives and defining polynomials are unchanged. -/
@[expose] def Context.queryPoly (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : DensePoly E :=
  if p.size ≤ 1 then p
  else if p.natDegree < context.root.raw.head.natDegree then p
  else context.queryRemainder p

/-- Constant queries retain the direct predecessor sign operation. -/
theorem Context.queryPoly_const (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : p.size ≤ 1) : context.queryPoly p = p := by
  simp only [queryPoly, h, ↓reduceIte]

/-- Every actual query has degree below the unchanged defining polynomial. -/
theorem Context.queryPoly_degree (context : Context E Ctx coeffSign parent) (p : DensePoly E) :
    (context.queryPoly p).natDegree < context.root.raw.head.natDegree := by
  have hw := (SignDet.RawDescriptor.check_eq context.root.accepted).1
  simp only [SignDet.RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hpos : 0 < context.root.raw.head.natDegree := hw.1.1.1.1
  have hhead : context.root.raw.head ≠ 0 := by
    intro h
    simp only [h, DensePoly.natDegree_zero, Nat.lt_irrefl] at hpos
  unfold queryPoly
  split
  · rename_i h
    rw [DensePoly.natDegree_eq_size_sub_one]
    omega
  · split
    · assumption
    · have hs := DensePoly.positivePseudoDiv_remainder_lt coeffSign p context.root.raw.head hhead
      rw [context.queryRemainder_eq]
      rw [DensePoly.natDegree_eq_size_sub_one]
      rw [DensePoly.natDegree_eq_size_sub_one] at hpos ⊢
      omega

/-- Selected-root signs use the bounded query without changing stored syntax.
The companion proves the preliminary pseudo-remainder preserves the sign;
the BKR certificate checks the reduced query. -/
@[expose] def Context.signPoly (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : Int := context.signQuery (context.queryPoly p)

theorem Context.signPoly_const (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : p.size ≤ 1) : context.signPoly p = coeffSign (p.coeff 0) := by
  rw [signPoly, context.queryPoly_const p h, context.signQuery_const p h]

theorem Context.monic_of_reduce (context : Context E Ctx coeffSign parent)
    (h : context.canReduce = true) : context.root.raw.head.leadingCoeff = 1 := by
  have hc := context.reduce_checked.symm.trans h
  by_cases hm : context.root.raw.head.leadingCoeff = 1
  · exact hm
  · simp [hm] at hc

/-- Compute and retain the exact monic remainder only for a clean definition.
Nonmonic or nonclean definitions keep the original representative. -/
@[expose] def Context.reduce (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) : DensePoly E :=
  if h : context.canReduce = true then
    (DensePoly.divModMonic p context.root.raw.head (context.monic_of_reduce h)).2
  else p

theorem Context.reduce_nonmonic (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : context.root.raw.head.leadingCoeff ≠ 1) :
    context.reduce p = p := by
  have hc : context.canReduce = false := by rw [context.reduce_checked]; simp [h]
  simp only [reduce, hc, Bool.false_eq_true, ↓reduceDIte]

theorem Context.reduce_unclean (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (h : context.root.raw.head.toArray.all context.cleanCoeff = false) :
    context.reduce p = p := by
  have hc : context.canReduce = false := by rw [context.reduce_checked, h, Bool.and_false]
  simp only [reduce, hc, Bool.false_eq_true, ↓reduceDIte]

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

/-- Restore the exact stored polynomial using a proved sign in this immutable
context. The proof is erased; this constructor performs no sign query and no
normalization. Zero retains its existing separate canonical representation. -/
def restore (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) : Element context :=
  ⟨some ⟨p, claimed, checked, nonzero⟩⟩

/-- Restore a literal nonzero stored form after checking its cached sign in
this exact context. Certificate coefficients must retain their polynomial;
arithmetic packing continues to use `ofPoly` and its reduction policy. -/
def restore? (p : DensePoly E) (claimed : Int) : Option (Element context) :=
  if hc : context.signPoly p = claimed then
    if hn : claimed ≠ 0 then some (restore p claimed hc hn) else none
  else none

/-- Proof-directed restoration gives the same literal result as the existing
independent executable sign check. -/
theorem restore?_eq (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) :
    restore? p claimed = some (restore p claimed checked nonzero) := by
  simp [restore?, restore, checked, nonzero]

private theorem stored_restore_proof (p : DensePoly E) (claimed : Int)
    (hc : context.signPoly p = claimed) (hn : claimed ≠ 0) :
    (restore? (context := context) p claimed).map Element.stored =
      some (some ⟨p, claimed, hc, hn⟩) := by
  simp [restore?, restore, hc, hn]

theorem stored_restore (p : DensePoly E) (claimed : Int)
    (hc : context.signPoly p = claimed) (hn : claimed ≠ 0) :
    (restore? (context := context) p claimed).map Element.stored =
      some (some ⟨p, claimed, hc, hn⟩) := stored_restore_proof p claimed hc hn

/-- Every existing nonzero restores literally, including representatives that
are semantically equal but structurally different. -/
private theorem restore_stored_proof (a : Element context) (p : Nonzero context)
    (h : a.stored = some p) : restore? p.polynomial p.sign = some a := by
  rcases a with ⟨stored⟩
  cases h
  simp [restore?, restore, p.checked, p.nonzero]

theorem restore_stored (a : Element context) (p : Nonzero context)
    (h : a.stored = some p) : restore? p.polynomial p.sign = some a :=
  restore_stored_proof a p h

theorem restore_zero (p : DensePoly E) :
    restore? (context := context) p 0 = none := by
  simp [restore?]

theorem restore_stale (p : DensePoly E) (claimed : Int)
    (h : context.signPoly p ≠ claimed) :
    restore? (context := context) p claimed = none := by
  simp [restore?, h]

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

private theorem ofPoly_restore_proof (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly (context.reduce p) = claimed) (nonzero : claimed ≠ 0) :
    ofPoly p = restore (context.reduce p) claimed checked nonzero := by
  apply ext
  simp [stored_ofPoly, restore, checked, nonzero]

/-- A proved sign of the actual retained remainder identifies packing with
proof-directed restoration. Kernel checking can reuse that scalar fact. -/
theorem ofPoly_restore (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly (context.reduce p) = claimed) (nonzero : claimed ≠ 0) :
    ofPoly p = restore (context.reduce p) claimed checked nonzero :=
  ofPoly_restore_proof p claimed checked nonzero

/-- A proved zero sign of the actual retained remainder identifies the
canonical zero branch of packing. -/
theorem ofPoly_zero (p : DensePoly E)
    (checked : context.signPoly (context.reduce p) = 0) :
    ofPoly (context := context) p = 0 := by
  apply ext
  simp [stored_ofPoly, checked, stored_zero]

@[expose] def polynomial (a : Element context) : DensePoly E :=
  match a.stored with
  | none => 0
  | some p => p.polynomial

/-- A polynomial whose coefficients are recursively clean. -/
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

private theorem restore_polynomial_proof (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) :
    (restore p claimed checked nonzero).polynomial = p := rfl

/-- Restoration retains the supplied representative, even when a monic
remainder would have a different literal form. -/
theorem restore_polynomial (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) :
    (restore p claimed checked nonzero).polynomial = p :=
  restore_polynomial_proof p claimed checked nonzero

private theorem restore_sign_proof (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) :
    (restore p claimed checked nonzero).sign = claimed := rfl

/-- Reading a proved restored sign performs no selected-root query. -/
theorem restore_sign (p : DensePoly E) (claimed : Int)
    (checked : context.signPoly p = claimed) (nonzero : claimed ≠ 0) :
    (restore p claimed checked nonzero).sign = claimed :=
  restore_sign_proof p claimed checked nonzero

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

/-- info: 'Hex.RealClosure.Algebraic.Context.queryPoly_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.queryPoly_degree
