/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignRequests
public import HexRealClosure.ContextOperations
public import HexSignDet.Codec

public section

namespace Hex.RealClosure.Algebraic.RootReplay
open SignDet

variable {E Ctx : Type} [zero : Zero E] [dec : DecidableEq E] [decCtx : DecidableEq Ctx]
variable [one : One E] [add : Add E] [neg : Neg E] [sub : Sub E]
variable [mul : Mul E] [inv : Inv E] [div : Div E] [natCast : NatCast E]

/-- Decode the complete root subject and all supplied graph entries before
checking a count-one descriptor. The predecessor codec may require exact
supplied sign facts; this reader does not replace missing coefficients. -/
@[expose] def readDescriptor (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : Codec.Json) :
    Except String (Descriptor E Ctx sign binding) := do
  let raw ← SignRequests.readRoot value ctx subject
  let graph ← Codec.readGraph value ctx binding raw.head raw.lower raw.upper evidence
  match graph.descriptor? sign binding raw with
  | none => throw "root descriptor replay rejected"
  | some descriptor => return descriptor

omit neg inv div in
/-- An accepted descriptor retains the entire decoded subject literally,
including its derivative indices and signs. -/
theorem readDescriptor_subject (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (subject evidence : Codec.Json)
    (descriptor : Descriptor E Ctx sign binding)
    (h : readDescriptor value ctx sign binding subject evidence = .ok descriptor) :
    SignRequests.readRoot value ctx subject = .ok descriptor.raw := by
  unfold readDescriptor at h
  cases hr : SignRequests.readRoot value ctx subject with
  | error message => simp [hr, bind, Except.bind] at h
  | ok raw =>
    simp only [hr, bind, Except.bind] at h
    cases hg : Codec.readGraph value ctx binding raw.head raw.lower raw.upper evidence with
    | error message => simp [hg] at h
    | ok graph =>
      simp only [hg] at h
      cases hd : graph.descriptor? sign binding raw with
      | none => simp [hd] at h
      | some checked =>
        simp only [hd, pure, Except.pure, Except.ok.injEq] at h
        subst descriptor
        rw [Dag.descriptor_raw hd]

/-- Reconstruct with equal supplied predecessor operations, including the
canonical prepared-query cache and reduction policy. Transport retains the checked
root and cache with the original operations. Ordinary-kernel assembly may stop at a
missing scalar fact; compiled execution retains the coefficient fallback. -/
@[expose] def readContext (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (clean : E → Bool)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add) (hn : predecessorNeg = neg)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul) (hi : predecessorInv = inv)
    (hd : predecessorDiv = div) (hc : predecessorNatCast = natCast)
    (subject evidence : Codec.Json) : Except String (@Context E Ctx zero dec one add neg sub mul inv div natCast
      decCtx sign binding) :=
  letI := predecessorOne
  letI := predecessorAdd
  letI := predecessorNeg
  letI := predecessorSub
  letI := predecessorMul
  letI := predecessorInv
  letI := predecessorDiv
  letI := predecessorNatCast
  do
    let root ← readDescriptor value ctx sign binding subject evidence
    let context := Context.adjoin root clean
    return @Context.changeOps E Ctx _ _ _ one add neg sub mul inv div natCast
      predecessorOne predecessorAdd predecessorNeg predecessorSub predecessorMul
      predecessorInv predecessorDiv predecessorNatCast ho ha hn hs hm hi hd hc
      sign binding context

/-- Supplied operations preserve exact native reconstruction, including
rejection. The equality assumes no completeness of the finite fact lists. -/
theorem readContext_eq (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (sign : E → Int) (binding : Ctx) (clean : E → Bool)
    (predecessorOne : One E) (predecessorAdd : Add E) (predecessorNeg : Neg E)
    (predecessorSub : Sub E) (predecessorMul : Mul E) (predecessorInv : Inv E)
    (predecessorDiv : Div E) (predecessorNatCast : NatCast E)
    (ho : predecessorOne = one) (ha : predecessorAdd = add) (hn : predecessorNeg = neg)
    (hs : predecessorSub = sub) (hm : predecessorMul = mul) (hi : predecessorInv = inv)
    (hd : predecessorDiv = div) (hc : predecessorNatCast = natCast)
    (subject evidence : Codec.Json) :
    @readContext E Ctx zero dec decCtx one add neg sub mul inv div natCast
      value ctx sign binding clean predecessorOne predecessorAdd predecessorNeg
      predecessorSub predecessorMul predecessorInv predecessorDiv predecessorNatCast
      ho ha hn hs hm hi hd hc subject evidence =
      (@readDescriptor E Ctx zero dec decCtx one add sub mul natCast
        value ctx sign binding subject evidence).map
        (fun root => @Context.adjoin E Ctx zero dec one add neg sub mul inv div natCast
          decCtx sign binding root clean) := by
  cases ho
  cases ha
  cases hn
  cases hs
  cases hm
  cases hi
  cases hd
  cases hc
  unfold readContext
  cases readDescriptor value ctx sign binding subject evidence with
  | error message => rfl
  | ok root =>
    simp only [bind, Except.bind, pure, Except.pure, Except.map]
    rw [Context.changeOps_self]

end Hex.RealClosure.Algebraic.RootReplay
