/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

/-- A finite packing record retains the original polynomial even when packing
returns canonical zero. Its joint replay records the representative's sign and
the zero difference between the original and retained representatives at the
same selected root. The stored value is the actual native packing result. -/
structure Packing (context : Context E Ctx coeffSign parent) where
  private mk ::
  original : DensePoly E
  representative : DensePoly E
  reduced : representative = context.reduce original
  value : Element context
  native : value = Element.ofPoly original
  sign : Int
  cached : value.sign = sign
  stored : value.polynomial = if sign = 0 then 0 else representative
  signs : SignDet.SelectedSigns context.root [representative, original - representative]
  observed : signs.values.toList = [sign, 0]

/-- Validate supplied packing evidence without producing a sign query. A fact
for the actual retained representative is required also in the constant case.
The supplied joint replay must bind the original polynomial's difference,
including for zero output. -/
def Packing.make? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E)
    (signs : SignDet.SelectedSigns context.root [reduce p, p - reduce p]) :
    Option (Packing context) :=
  match hf : SignFact.find facts (reduce p) with
  | none => none
  | some f =>
    if observed : signs.values.toList = [f.val, 0] then
      some ⟨p, reduce p, congrFun hr p, Element.pack reduce hr facts p,
        Element.pack_eq reduce hr facts p, f.val, by
          unfold Element.pack
          dsimp only
          rw [hf]
          dsimp only
          split
          · rename_i zero
            rw [Element.sign_zero]
            exact zero.symm
          · unfold Element.sign
            rw [Element.stored_restore]
        , by
          unfold Element.pack
          dsimp only
          rw [hf]
          dsimp only
          split
          · exact Element.polynomial_zero
          · unfold Element.polynomial
            rw [Element.stored_restore]
        , signs, observed⟩
    else none

/-- Successful reading retains the actual request, reducer and cached native
packing result rather than merely a polynomial with the same sign. -/
theorem Packing.make?_bindings (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E)
    (signs : SignDet.SelectedSigns context.root [reduce p, p - reduce p])
    {entry : Packing context} (accepted : Packing.make? reduce hr facts p signs = some entry) :
    entry.original = p ∧ entry.representative = reduce p ∧
      entry.value = Element.pack reduce hr facts p := by
  unfold Packing.make? at accepted
  split at accepted
  · contradiction
  ·
    split at accepted
    · cases Option.some.inj accepted
      exact ⟨rfl, rfl, rfl⟩
    · contradiction

/-- Read the joint packing record from supplied checked graph entries. Every
context, root-domain and operand binding goes through the existing strict
selected-sign reader. No isolation or BKR production is invoked. -/
def Packing.readMemo? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper))
    (index : Nat) : Option (Packing context) :=
  match SignFact.find facts (reduce p) with
  | none => none
  | some fact => do
    let signs ← SignDet.SelectedSigns.readMemo? context.root [reduce p, p - reduce p]
      #v[fact.val, 0] memo index
    Packing.make? reduce hr facts p signs

/-- The producer obtains a complete joint replay, then uses the same finite
reader. Supplied scalar facts still bind the actual reduced key. -/
def Packing.build? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E) : Option (Packing context) := do
  let .ok signs := context.buildSigns [reduce p, p - reduce p] | none
  Packing.make? reduce hr facts p signs

/-- Successful production retains the original key, reduction and native value. -/
theorem Packing.build?_bindings (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (p : DensePoly E) {entry : Packing context}
    (accepted : Packing.build? reduce hr facts p = some entry) :
    entry.original = p ∧ entry.representative = reduce p ∧
      entry.value = Element.pack reduce hr facts p := by
  unfold Packing.build? at accepted
  cases produced : context.buildSigns [reduce p, p - reduce p] with
  | error error => simp [produced] at accepted
  | ok signs =>
    simp only [produced] at accepted
    exact Packing.make?_bindings reduce hr facts p signs accepted

/-- Lookup uses the original request, including when several nonzero
polynomials all pack to canonical zero. The inventory retains their separate
raw equations and checked joint replays. -/
@[expose] def Packing.find (entries : List (Packing context)) (p : DensePoly E) :
    Option (Packing context) :=
  match entries with
  | [] => none
  | entry :: rest =>
    if entry.original = p then some entry
    else Packing.find rest p

/-- A found record binds the actual original key and native value. Keeping the
record in the lookup result also retains its joint replay during assembly. -/
theorem Packing.find_native (entries : List (Packing context)) (p : DensePoly E)
    {entry : Packing context} (found : Packing.find entries p = some entry) :
    entry.original = p ∧ entry.value = Element.ofPoly p := by
  induction entries with
  | nil => simp [Packing.find] at found
  | cons first rest ih =>
    unfold Packing.find at found
    split at found
    · rename_i key
      cases Option.some.inj found
      exact ⟨key, key ▸ entry.native⟩
    · exact ih found

/-- Ordinary-kernel assembly stops at every unrecorded original packing,
including constants, successful cached signs and zero outputs. Unlike the
scalar-sign cache, a record for a reduced key cannot cover a different raw
request. Compiled fallback is native packing, so this is an assembly boundary,
not a strict checker for untrusted compiled replay. -/
@[expose] def Element.replayPack (entries : List (Packing context)) (p : DensePoly E) :
    Element context :=
  match Packing.find entries p with
  | none => (Element.missing p).val
  | some result => result.value

/-- Recording all packings changes no native value or field operation. -/
theorem Element.replayPack_eq (entries : List (Packing context)) (p : DensePoly E) :
    Element.replayPack entries p = Element.ofPoly p := by
  unfold Element.replayPack
  cases found : Packing.find entries p with
  | none => exact (Element.missing p).property
  | some result => exact (Packing.find_native entries p found).2

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Packing.make?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.make?

/-- info: 'Hex.RealClosure.Algebraic.Packing.make?_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.make?_bindings

/-- info: 'Hex.RealClosure.Algebraic.Packing.build?_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.build?_bindings

/-- info: 'Hex.RealClosure.Algebraic.Packing.find_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.find_native

/-- info: 'Hex.RealClosure.Algebraic.Element.replayPack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.replayPack_eq
