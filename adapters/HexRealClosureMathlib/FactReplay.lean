/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SignEvidence
import all HexRealClosureMathlib.SignEvidence
public import HexRealClosure.ContextOperations

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} {K : Type v} [zero : Zero E] [dec : DecidableEq E]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]
variable [decCtx : DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hsign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

local notation "Fact" =>
  @SignFact E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent

/-- Check one supplied joint packet with equal coefficient operations, and
return its proved scalar facts in the original immutable context. All entries
are checked once by the existing reader. Supplied-fact operations can stop
ordinary-kernel evaluation at a missing lower fact; compiled execution retains
those operations' native fallback. The interpretation occurs only in proofs. -/
@[expose, macro_inline] def Context.readEvidenceWith? (context : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (hadd : predecessorAdd = add) (hneg : predecessorNeg = neg)
    (hsub : predecessorSub = sub) (hmul : predecessorMul = mul) (hinv : predecessorInv = inv)
    (hdiv : predecessorDiv = div) (hcast : predecessorNatCast = natCast)
    (required : List (DensePoly E)) (evidence : SignEvidence E Ctx) :
    Option (Vector (Fact context) required.length) :=
  letI := predecessorOne
  letI := predecessorAdd
  letI := predecessorNeg
  letI := predecessorSub
  letI := predecessorMul
  letI := predecessorInv
  letI := predecessorDiv
  letI := predecessorNatCast
  let current := @Context.changeOps E Ctx zero dec decCtx
    predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
    predecessorInv predecessorDiv predecessorNatCast one add neg sub mul inv div natCast
    ho.symm hadd.symm hneg.symm hsub.symm hmul.symm hinv.symm hdiv.symm hcast.symm
    coeffSign parent context
  do
    let facts ← current.readEvidence? f hz
      (by
        change f (@One.one E predecessorOne) = 1
        rw [ho]
        exact h1)
      (by
        intro a b
        change f (@Add.add E predecessorAdd a b) = _
        rw [hadd]
        exact ha a b)
      (by
        intro a b
        change f (@Sub.sub E predecessorSub a b) = _
        rw [hsub]
        exact hs a b)
      (by
        intro a b
        change f (@Mul.mul E predecessorMul a b) = _
        rw [hmul]
        exact hm a b)
      (by
        intro n
        change f (@NatCast.natCast E predecessorNatCast n) = _
        rw [hcast]
        exact hnat n)
      hsign (by intro a; rw [hneg]; exact hn a)
      (by intro a; rw [hinv]; exact hi a)
      required evidence
    return facts.map fun fact =>
      @SignFact.mk E Ctx zero dec one add neg sub mul inv div natCast decCtx
        coeffSign parent context fact.polynomial fact.sign (by
          have same := @Context.changeOps_signPoly E Ctx zero dec decCtx
            predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
            predecessorInv predecessorDiv predecessorNatCast one add neg sub mul inv div natCast
            ho.symm hadd.symm hneg.symm hsub.symm hmul.symm hinv.symm hdiv.symm hcast.symm
            coeffSign parent context
          exact (congrFun same fact.polynomial).symm.trans fact.checked)

private theorem readEvidence_map (source target : Context E Ctx coeffSign parent)
    (same : source = target) (required : List (DensePoly E)) (evidence : SignEvidence E Ctx) :
    (source.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence).map
      (fun facts => facts.map fun fact =>
        (⟨fact.polynomial, fact.sign, by cases same; exact fact.checked⟩ : Fact target)) =
      target.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence := by
  cases same
  cases h : source.readEvidence? f hz h1 ha hs hm hnat hsign hn hi required evidence with
  | none => rfl
  | some facts =>
    simp only [Option.map_some, Option.some.injEq]
    change facts.map id = facts
    exact Vector.map_id facts

/-- Equal supplied operations preserve the complete reader result, including
rejection and every exact key and sign. No finite-fact completeness hypothesis
is required. -/
theorem Context.readEvidenceWith_eq (context : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (hadd : predecessorAdd = add) (hneg : predecessorNeg = neg)
    (hsub : predecessorSub = sub) (hmul : predecessorMul = mul) (hinv : predecessorInv = inv)
    (hdiv : predecessorDiv = div) (hcast : predecessorNatCast = natCast)
    (required : List (DensePoly E)) (evidence : SignEvidence E Ctx) :
    @Context.readEvidenceWith? E Ctx K zero dec one add neg sub mul inv div natCast
      decCtx coeffSign parent _ _ _ _ _ f hz h1 ha hs hm hnat hsign hn hi context
      predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
      predecessorInv predecessorDiv predecessorNatCast ho hadd hneg hsub hmul hinv hdiv hcast
      required evidence =
      @Context.readEvidence? E Ctx K zero dec one add neg sub mul inv div natCast
        decCtx coeffSign parent _ _ _ _ _ f hz h1 ha hs hm hnat hsign hn hi
        context required evidence := by
  cases ho
  cases hadd
  cases hneg
  cases hsub
  cases hmul
  cases hinv
  cases hdiv
  cases hcast
  unfold Context.readEvidenceWith?
  dsimp only
  simpa only [Option.map_eq_bind, Function.comp_def, bind, pure] using
    readEvidence_map f hz h1 ha hs hm hnat hsign hn hi _ context
      (Context.changeOps_self coeffSign parent context) required evidence

/-- Decode a context-bound joint packet with the supplied predecessor codec,
then check it with the equal supplied arithmetic. Missing stored coefficient
facts reject during decoding; missing intermediate facts block kernel evaluation. -/
@[expose, macro_inline] def Context.decodeEvidenceWith (context : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (hadd : predecessorAdd = add) (hneg : predecessorNeg = neg)
    (hsub : predecessorSub = sub) (hmul : predecessorMul = mul) (hinv : predecessorInv = inv)
    (hdiv : predecessorDiv = div) (hcast : predecessorNatCast = natCast)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (required : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits := {}) :
    Except String (Vector (Fact context) required.length) := do
  let root := @Context.root E Ctx zero dec one add neg sub mul inv div natCast decCtx
    coeffSign parent context
  let raw := @Descriptor.raw E Ctx zero dec one add sub mul natCast decCtx
    coeffSign parent root
  let evidence ← (SignEvidence.codec value ctx raw).decodeBytes input limits
  match @Context.readEvidenceWith? E Ctx K zero dec one add neg sub mul inv div natCast
      decCtx coeffSign parent _ _ _ _ _ f hz h1 ha hs hm hnat hsign hn hi context
      predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
      predecessorInv predecessorDiv predecessorNatCast ho hadd hneg hsub hmul hinv hdiv hcast required evidence with
  | none => throw "child sign evidence rejected"
  | some facts => return facts

/-- The complete byte reader preserves the ordinary reader's result for every
input, including rejection. The supplied codec need not cover every coefficient. -/
theorem Context.decodeEvidenceWith_eq (context : Context E Ctx coeffSign parent)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (hadd : predecessorAdd = add) (hneg : predecessorNeg = neg)
    (hsub : predecessorSub = sub) (hmul : predecessorMul = mul) (hinv : predecessorInv = inv)
    (hdiv : predecessorDiv = div) (hcast : predecessorNatCast = natCast)
    (value : ValueCodec E) (ctx : ValueCodec Ctx) (required : List (DensePoly E))
    (input : ByteArray) (limits : Codec.Limits := {}) :
    @Context.decodeEvidenceWith E Ctx K zero dec one add neg sub mul inv div natCast
      decCtx coeffSign parent _ _ _ _ _ f hz h1 ha hs hm hnat hsign hn hi context
      predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
      predecessorInv predecessorDiv predecessorNatCast ho hadd hneg hsub hmul hinv hdiv hcast value ctx required input limits =
      @Context.decodeEvidence E Ctx K zero dec one add neg sub mul inv div natCast
        decCtx coeffSign parent _ _ _ _ _ f hz h1 ha hs hm hnat hsign hn hi
        context value ctx required input limits := by
  unfold Context.decodeEvidenceWith Context.decodeEvidence
  dsimp only
  simp only [Context.readEvidenceWith_eq, bind, Except.bind, pure, Except.pure]
  split
  · rfl
  · split <;> simp_all

end Hex.RealClosure.Algebraic
