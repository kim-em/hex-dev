/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Algebraic
public import HexSignDet.DagSelectedSigns

public section

namespace Hex.RealClosure.Algebraic

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}

/-- A proved scalar sign, keyed by the exact stored polynomial and context. -/
structure SignFact (context : Context E Ctx coeffSign parent) where
  polynomial : DensePoly E
  sign : Int
  checked : context.signPoly polynomial = sign

variable {context : Context E Ctx coeffSign parent}

/-- Select supplied evidence for the scalar operation's actual reduced query.
All executable query/domain/row checks stay in the Mathlib-free core. -/
@[expose] def Context.readSigns? (context : Context E Ctx coeffSign parent)
    (p : DensePoly E) (claimed : Int) {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (SignDet.SelectedSigns context.root [context.queryPoly p]) :=
  SignDet.SelectedSigns.readMemo? context.root [context.queryPoly p] #v[claimed] memo index

theorem Context.readSigns_value {context : Context E Ctx coeffSign parent}
    {p : DensePoly E} {claimed : Int} {head : DensePoly E} {lower upper : Endpoint E}
    {memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)} {index : Nat}
    {signs : SignDet.SelectedSigns context.root [context.queryPoly p]}
    (h : context.readSigns? p claimed memo index = some signs) : signs.value = claimed := by
  obtain ⟨bound, _, accepted⟩ := SignDet.SelectedSigns.readMemo_evidence h
  obtain ⟨_, _, values, _⟩ := SignDet.SelectedSigns.ofMemo_evidence accepted
  simp [SignDet.SelectedSigns.value, values]

/-- Literal lookup retains the proof belonging to that precise key. -/
@[expose] def SignFact.find (facts : List (SignFact context)) (p : DensePoly E) :
    Option {s : Int // context.signPoly p = s} :=
  match facts with
  | [] => none
  | f :: fs =>
    if h : f.polynomial = p then some ⟨f.sign, h ▸ f.checked⟩
    else SignFact.find fs p

/-- Restore a supplied nonzero literal only when the finite facts contain its
exact polynomial and claimed sign. Missing keys do not start a sign search. -/
@[expose] def SignFact.read (facts : List (SignFact context)) (p : DensePoly E)
    (claimed : Int) : Option (Element context) :=
  match SignFact.find facts p with
  | none => none
  | some f =>
    if hc : f.val = claimed then
      if hn : claimed ≠ 0 then
        some (Element.restore p claimed (f.property.trans hc) hn)
      else none
    else none

/-- Successful lookup preserves the native decoder's literal result. -/
theorem SignFact.read_sound (facts : List (SignFact context)) (p : DensePoly E)
    (s : Int) (a : Element context) (h : SignFact.read facts p s = some a) :
    Element.restore? p s = some a := by
  unfold read at h
  cases hf : SignFact.find facts p with
  | none => simp only [hf] at h; contradiction
  | some f =>
    simp only [hf] at h
    split at h
    · rename_i hc
      split at h
      · rename_i hn
        cases Option.some.inj h
        exact Element.restore?_eq p s (f.property.trans hc) hn
      · contradiction
    · contradiction

private theorem restore_congr (p q : DensePoly E) (s : Int)
    (hp : context.signPoly p = s) (hq : context.signPoly q = s)
    (hn : s ≠ 0) (h : p = q) :
    Element.restore p s hp hn = Element.restore q s hq hn := by
  cases h
  rfl

/-- The ordinary kernel cannot evaluate this missing-fact branch. Its
erased property still establishes equality with native packing. Compiled
evaluation runs native packing; this is a kernel assembly boundary, not a
strict checker for untrusted compiled replay. -/
opaque Element.missing (p : DensePoly E) :
    {a : Element context // a = Element.ofPoly p} := ⟨Element.ofPoly p, rfl⟩

/-- Pack with supplied signs of the exact retained remainders. A proved
reduction function avoids evaluating the context constructor in the kernel.
Constant remainders use the ordinary predecessor sign; a missing nonconstant
fact stops ordinary-kernel evaluation at `Element.missing`. -/
@[expose] def Element.pack (reduce : DensePoly E → DensePoly E)
    (_hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E) : Element context :=
  let kept := reduce p
  if hc : kept.size ≤ 1 then
    let s := coeffSign (kept.coeff 0)
    if hn : s = 0 then 0
    else Element.restore kept s (context.signPoly_const kept hc) hn
  else
    match SignFact.find facts kept with
    | none => (Element.missing p).val
    | some f =>
      if hn : f.val = 0 then 0
      else Element.restore kept f.val f.property hn

/-- A missing nonconstant fact reaches exactly the opaque packing boundary. -/
theorem Element.pack_missing (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E)
    (hc : ¬ (reduce p).size ≤ 1) (hf : SignFact.find facts (reduce p) = none) :
    Element.pack reduce hr facts p = (Element.missing p).val := by
  simp only [Element.pack, dite_eq_right hc, hf]

/-- Cached packing agrees literally with the actual native reduction policy. -/
theorem Element.pack_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) (p : DensePoly E) :
    Element.pack reduce hr facts p = Element.ofPoly p := by
  have restore_eq (s : Int) (hc : context.signPoly (reduce p) = s) (hn : s ≠ 0) :
      Element.restore (reduce p) s hc hn = Element.ofPoly p := by
    have hc' : context.signPoly (context.reduce p) = s := by rw [← hr]; exact hc
    exact ((Element.ofPoly_restore p s hc' hn).trans
      (restore_congr _ _ _ hc' hc hn (congrFun hr.symm p))).symm
  have zero_eq (hc : context.signPoly (reduce p) = 0) :
      (0 : Element context) = Element.ofPoly p := by
    apply (Element.ofPoly_eq_zero p _).symm
    rw [← hr]
    exact hc
  unfold pack
  dsimp only
  split
  · rename_i hc
    split
    · rename_i hn
      exact zero_eq ((context.signPoly_const _ hc).trans hn)
    · exact restore_eq _ (context.signPoly_const _ hc) (by assumption)
  · cases hf : SignFact.find facts (reduce p) with
    | none => simpa only using (Element.missing p).property
    | some f =>
      simp only
      split
      · rename_i hn
        exact zero_eq (f.property.trans hn)
      · exact restore_eq _ f.property (by assumption)

@[expose, instance_reducible] def Element.cachedAdd (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : Add (Element context) :=
  ⟨fun a b => Element.pack reduce hr facts (a.polynomial + b.polynomial)⟩

theorem Element.cachedAdd_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedAdd reduce hr facts = (inferInstance : Add (Element context)) := by
  apply congrArg Add.mk
  funext a b
  exact Element.pack_eq reduce hr facts _

@[expose, instance_reducible] def Element.cachedSub (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : Sub (Element context) :=
  ⟨fun a b => Element.pack reduce hr facts (a.polynomial - b.polynomial)⟩

theorem Element.cachedSub_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedSub reduce hr facts = (inferInstance : Sub (Element context)) := by
  apply congrArg Sub.mk
  funext a b
  exact Element.pack_eq reduce hr facts _

@[expose, instance_reducible] def Element.cachedMul (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : Mul (Element context) :=
  ⟨fun a b => Element.pack reduce hr facts (a.polynomial * b.polynomial)⟩

theorem Element.cachedMul_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedMul reduce hr facts = (inferInstance : Mul (Element context)) := by
  apply congrArg Mul.mk
  funext a b
  exact Element.pack_eq reduce hr facts _

@[expose, instance_reducible] def Element.cachedNeg (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : Neg (Element context) :=
  ⟨fun a => Element.pack reduce hr facts (0 - a.polynomial)⟩

theorem Element.cachedNeg_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedNeg reduce hr facts = (inferInstance : Neg (Element context)) := by
  apply congrArg Neg.mk
  funext a
  exact Element.pack_eq reduce hr facts _

@[expose, instance_reducible] def Element.cachedOne (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : One (Element context) :=
  ⟨Element.pack reduce hr facts 1⟩

theorem Element.cachedOne_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedOne reduce hr facts = (inferInstance : One (Element context)) := by
  apply congrArg One.mk
  exact Element.pack_eq reduce hr facts _

@[expose, instance_reducible] def Element.cachedNatCast (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) : NatCast (Element context) :=
  ⟨fun n => Element.pack reduce hr facts (DensePoly.C n)⟩

theorem Element.cachedNatCast_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context)) :
    Element.cachedNatCast reduce hr facts = (inferInstance : NatCast (Element context)) := by
  apply congrArg NatCast.mk
  funext n
  exact Element.pack_eq reduce hr facts _

end Hex.RealClosure.Algebraic
