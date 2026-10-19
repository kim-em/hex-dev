/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.SignFacts
public import HexRealClosure.ContextOperations
public import HexRealClosure.RecordOperations

public section
namespace Hex.RealClosure.Algebraic

variable {E Ctx : Type} {K : Type v} [zero : Zero E] [dec : DecidableEq E]
variable [ordinaryOne : One E] [ordinaryAdd : Add E] [ordinaryNeg : Neg E]
variable [ordinarySub : Sub E] [ordinaryMul : Mul E] [ordinaryInv : Inv E]
variable [ordinaryDiv : Div E] [ordinaryNatCast : NatCast E] [decCtx : DecidableEq Ctx]
variable {coeffSign : E → Int} {parent : Ctx}
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (hAdd : ∀ a b, f (a + b) = f a + f b)
variable (hSub : ∀ a b, f (a - b) = f a - f b)
variable (hMul : ∀ a b, f (a * b) = f a * f b)
variable (hNat : ∀ n : Nat, f (n : E) = (n : K))
variable (hSign : ∀ a, coeffSign a = (SignType.sign (f a) : Int))
variable (hNeg : ∀ a, f (-a) = -f a) (hInv : ∀ a, f a⁻¹ = (f a)⁻¹)


/-- Compute the original scalar query with equal cached dictionaries. The
changed context is used only to access the retained root and reduction policy. -/
@[expose] def Context.queryOperations (context : Context E Ctx coeffSign parent)
    (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hg : neg = ordinaryNeg)
    (hs : sub = ordinarySub) (hm : mul = ordinaryMul) (hi : inv = ordinaryInv)
    (hd : div = ordinaryDiv) (hn : natCast = ordinaryNatCast) (p : DensePoly E) : DensePoly E :=
  let alternate := @Context.changeOps E Ctx zero dec decCtx one add neg sub mul inv div natCast
    ordinaryOne ordinaryAdd ordinaryNeg ordinarySub ordinaryMul ordinaryInv ordinaryDiv ordinaryNatCast
    ho.symm ha.symm hg.symm hs.symm hm.symm hi.symm hd.symm hn.symm coeffSign parent context
  @Context.queryPoly E Ctx zero dec one add neg sub mul inv div natCast decCtx coeffSign parent
    alternate p

theorem Context.queryOperations_eq (context : Context E Ctx coeffSign parent)
    (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hg : neg = ordinaryNeg)
    (hs : sub = ordinarySub) (hm : mul = ordinaryMul) (hi : inv = ordinaryInv)
    (hd : div = ordinaryDiv) (hn : natCast = ordinaryNatCast) (p : DensePoly E) :
    letI := ordinaryOne
    letI := ordinaryAdd
    letI := ordinaryNeg
    letI := ordinarySub
    letI := ordinaryMul
    letI := ordinaryInv
    letI := ordinaryDiv
    letI := ordinaryNatCast
    context.queryOperations one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn p =
      @Context.queryPoly E Ctx zero dec ordinaryOne ordinaryAdd ordinaryNeg ordinarySub ordinaryMul
        ordinaryInv ordinaryDiv ordinaryNatCast decCtx coeffSign parent context p := by
  cases ho; cases ha; cases hg; cases hs; cases hm; cases hi; cases hd; cases hn
  simp only [queryOperations, Context.changeOps_self]

/-- Select the original query from an already checked native memo, computing
only its query and derivative prefix with equal supplied implementations.
Acceptance checks the exact original ordered query list and selected row. -/
@[expose, macro_inline] def Context.readQuerySigns?
    (context : Context E Ctx coeffSign parent) (p : DensePoly E) (claimed : Int)
    (query : DensePoly E) (hq : query = context.queryPoly p)
    (queries : List (DensePoly E)) (hqs : queries = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (SignDet.SelectedSigns context.root [context.queryPoly p]) := do
  let bound ← SignDet.Dag.bindDomain? coeffSign parent memo
    context.root.raw.head context.root.raw.lower context.root.raw.upper
  let tree ← SignDet.Dag.select? coeffSign parent context.root.raw.head
    context.root.raw.lower context.root.raw.upper bound index (queries ++ [query])
  if row : tree.val.node.system.tableRows.toList.filter
      (fun entry => decide (entry.1.take queries.length = context.root.raw.signs)) =
      [(context.root.raw.signs ++ [claimed], 1)] then
    return SignDet.SelectedSigns.ofTable context.root [context.queryPoly p] #v[claimed]
      tree.val (by simpa only [hq, hqs] using tree.property)
      (by simpa [hqs] using row)
  else none


/-- Identity query and prefix implementations give the native selected-sign
reader definitionally. Only the checked acceptance proof is transported. -/
theorem Context.readQuerySigns_eq
    (context : Context E Ctx coeffSign parent) (p : DensePoly E) (claimed : Int)
    (query : DensePoly E) (hq : query = context.queryPoly p)
    (queries : List (DensePoly E)) (hqs : queries = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    context.readQuerySigns? p claimed query hq queries hqs memo index =
      context.readSigns? p claimed memo index := by
  cases hq
  cases hqs
  rfl

/-- Scalar replay using equal query arithmetic and derivative prefixes,
retaining the original owner and literal request in the returned fact. -/
@[expose, macro_inline] def Context.readSignQuery?
    (context : Context E Ctx coeffSign parent) (p : DensePoly E) (claimed : Int)
    (query : DensePoly E) (hq : query = context.queryPoly p)
    (queries : List (DensePoly E)) (hqs : queries = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    Option (SignFact context) :=
  match h : context.readQuerySigns? p claimed query hq queries hqs memo index with
  | none => none
  | some signs => some ⟨p, claimed, by
      have selected : context.readSigns? p claimed memo index = some signs :=
        (context.readQuerySigns_eq p claimed query hq queries hqs memo index).symm.trans h
      exact (context.signPoly_checked f hz h1 hAdd hSub hMul hNat hSign hNeg hInv p signs).trans
        (Context.readSigns_value selected)⟩

/-- Query implementations preserve the complete scalar result, including
rejection, without requiring complete finite inventories. -/
theorem Context.readSignQuery_eq
    (context : Context E Ctx coeffSign parent) (p : DensePoly E) (claimed : Int)
    (query : DensePoly E) (hq : query = context.queryPoly p)
    (queries : List (DensePoly E)) (hqs : queries = context.root.raw.queries)
    {head : DensePoly E} {lower upper : Endpoint E}
    (memo : Array (SignDet.Dag.Checked coeffSign parent head lower upper)) (index : Nat) :
    context.readSignQuery? f hz h1 hAdd hSub hMul hNat hSign hNeg hInv p claimed
      query hq queries hqs memo index =
    context.readSignFact? f hz h1 hAdd hSub hMul hNat hSign hNeg hInv p claimed memo index := by
  cases hq
  cases hqs
  rfl

/-- Check literal graph data with cached predecessor arithmetic and sign
records, then select the original scalar query from the restored checked memo.
The immutable owner and its complete cached root data remain unchanged. -/
@[expose, macro_inline] def Context.readSignOperations?
    (context : Context E Ctx coeffSign parent)
    (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hg : neg = ordinaryNeg)
    (hs : sub = ordinarySub) (hm : mul = ordinaryMul) (hi : inv = ordinaryInv)
    (hd : div = ordinaryDiv) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (same : sign = coeffSign)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    (p : DensePoly E) (claimed : Int) (packet : SignDet.Codec.Json) :
    Option (@SignFact E Ctx zero dec ordinaryOne ordinaryAdd ordinaryNeg ordinarySub
      ordinaryMul ordinaryInv ordinaryDiv ordinaryNatCast decCtx coeffSign parent context) :=
  letI := ordinaryOne
  letI := ordinaryAdd
  letI := ordinaryNeg
  letI := ordinarySub
  letI := ordinaryMul
  letI := ordinaryInv
  letI := ordinaryDiv
  letI := ordinaryNatCast
  let raw := context.root.raw
  let query := context.queryOperations one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn p
  let queryEqual := context.queryOperations_eq one add neg sub mul inv div natCast
    ho ha hg hs hm hi hd hn p
  let queries := @SignDet.RawDescriptor.queries E Ctx zero dec natCast mul raw
  have prefixEqual : queries = raw.queries := by
    cases hn
    cases hm
    rfl
  do
    let graph ← (SignDet.Codec.readGraph value ctx parent raw.head raw.lower raw.upper packet).toOption
    let memo ← Hex.RealClosure.Replay.validateOperations? one add sub mul natCast ho ha hs hm hn
      sign coeffSign same parent raw.head raw.lower raw.upper graph
    context.readSignQuery? f hz h1 hAdd hSub hMul hNat hSign hNeg hInv p claimed
      query queryEqual queries prefixEqual memo graph.root

/-- Cached operations preserve the complete native packet result, including
rejection, without assuming that any finite inventory is complete. -/
theorem Context.readSignOperations_eq
    (context : Context E Ctx coeffSign parent)
    (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = ordinaryOne) (ha : add = ordinaryAdd) (hg : neg = ordinaryNeg)
    (hs : sub = ordinarySub) (hm : mul = ordinaryMul) (hi : inv = ordinaryInv)
    (hd : div = ordinaryDiv) (hn : natCast = ordinaryNatCast)
    (sign : E → Int) (same : sign = coeffSign)
    (value : SignDet.ValueCodec E) (ctx : SignDet.ValueCodec Ctx)
    (p : DensePoly E) (claimed : Int) (packet : SignDet.Codec.Json) :
    letI := ordinaryOne
    letI := ordinaryAdd
    letI := ordinaryNeg
    letI := ordinarySub
    letI := ordinaryMul
    letI := ordinaryInv
    letI := ordinaryDiv
    letI := ordinaryNatCast
    context.readSignOperations? f hz h1 hAdd hSub hMul hNat hSign hNeg hInv
      one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn sign same
      value ctx p claimed packet =
    context.readSignPacket? f hz h1 hAdd hSub hMul hNat hSign hNeg hInv
      value ctx p claimed packet := by
  unfold readSignOperations?
  simp_rw [Hex.RealClosure.Replay.validateOperations_eq, Context.readSignQuery_eq]
  rfl

end Hex.RealClosure.Algebraic
