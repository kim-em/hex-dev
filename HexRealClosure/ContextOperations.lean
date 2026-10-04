/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Algebraic
public import HexSignDet.HandleOperations

public section

namespace Hex.RealClosure.Algebraic.Context

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [targetOne : One E] [targetAdd : Add E] [targetNeg : Neg E] [targetSub : Sub E]
variable [targetMul : Mul E] [targetInv : Inv E] [targetDiv : Div E] [targetNatCast : NatCast E]

/-- Change equal coefficient operations while retaining the checked root,
prepared cache, count and reduction policy. All transport is confined to proofs. -/
@[expose] def changeOps (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hg : neg = targetNeg) (hs : sub = targetSub)
    (hm : mul = targetMul) (hi : inv = targetInv) (hd : div = targetDiv)
    (hn : natCast = targetNatCast) (sign : E → Int) (binding : Ctx)
    (context : @Context E Ctx _ _ one add neg sub mul inv div natCast _ sign binding) :
    @Context E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
      targetNatCast _ sign binding :=
  let source := @Context.root E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context
  let root := @SignDet.Descriptor.changeOps E Ctx _ _ _ targetOne targetAdd targetSub
    targetMul targetNatCast one add sub mul natCast ho ha hs hm hn sign binding source
  let cached := @Context.handle E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context
  let handle := cached.map (@SignDet.QueryHandle.changeOps E Ctx _ _ _ targetOne targetAdd
    targetSub targetMul targetNatCast targetNeg targetInv one add sub mul natCast neg inv
    ho ha hs hm hn hg hi sign binding source)
  let rootCount := @Context.rootCount E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context
  let clean := @Context.cleanCoeff E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context
  let canReduce := @Context.canReduce E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context
  @Context.ofChecked E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
    targetNatCast _ sign binding root handle
    (by
      cases ho
      cases ha
      cases hg
      cases hs
      cases hm
      cases hi
      cases hd
      cases hn
      have same := SignDet.Descriptor.changeOps_self sign binding source
      have cacheSame := SignDet.QueryHandle.map_heq source root same
        (SignDet.QueryHandle.changeOps targetOne targetAdd targetSub targetMul targetNatCast
          targetNeg targetInv rfl rfl rfl rfl rfl rfl rfl sign binding source)
        (SignDet.QueryHandle.changeOps_self sign binding source) cached
      have preparedSame := SignDet.Descriptor.prepareQueries_heq source root same
      exact eq_of_heq (HEq.trans cacheSame
        (HEq.trans (heq_of_eq context.handle_checked) (HEq.symm preparedSame))))
    rootCount
    (by
      cases ho
      cases ha
      cases hg
      cases hs
      cases hm
      cases hi
      cases hd
      cases hn
      have counts : handle.map (fun h => Sturm.countPrepared h.domain) =
          cached.map (fun h => Sturm.countPrepared h.domain) := by
        dsimp only [handle]
        rw [Option.map_map]
        congr 1
        funext h
        dsimp only [Function.comp_def]
        have sameDomain := @SignDet.QueryHandle.changeOps_domain E Ctx _ _ _ targetOne
          targetAdd targetSub targetMul targetNatCast targetNeg targetInv targetOne targetAdd
          targetSub targetMul targetNatCast targetNeg targetInv rfl rfl rfl rfl rfl rfl rfl
          sign binding source h
        rw [Sturm.PreparedDomain.changeOps_self] at sameDomain
        exact congrArg Sturm.countPrepared sameDomain
      exact context.count_checked.trans counts.symm)
    clean canReduce
    (by
      cases ho
      cases ha
      cases hg
      cases hs
      cases hm
      cases hi
      cases hd
      cases hn
      simpa only [source, root, clean, canReduce, SignDet.Descriptor.changeOps_self]
        using context.reduce_checked)

/-- Operation transport retains the literal root subject, count and
reduction policy. This observation needs no access to private constructors. -/
theorem changeOps_data (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hg : neg = targetNeg) (hs : sub = targetSub)
    (hm : mul = targetMul) (hi : inv = targetInv) (hd : div = targetDiv)
    (hn : natCast = targetNatCast) (sign : E → Int) (binding : Ctx)
    (context : @Context E Ctx _ _ one add neg sub mul inv div natCast _ sign binding) :
    (@SignDet.Descriptor.raw E Ctx _ _ targetOne targetAdd targetSub targetMul targetNatCast _
        sign binding (@Context.root E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
      targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context)),
      @Context.rootCount E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv
        targetDiv targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context),
      @Context.cleanCoeff E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv
        targetDiv targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context),
      @Context.canReduce E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv
        targetDiv targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context)) =
    (@SignDet.Descriptor.raw E Ctx _ _ one add sub mul natCast _ sign binding (@Context.root E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context),
      @Context.rootCount E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context,
      @Context.cleanCoeff E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context,
      @Context.canReduce E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context) := by
  unfold changeOps
  simp only [@Context.ofChecked_root, @Context.ofChecked_rootCount,
    @Context.ofChecked_cleanCoeff, @Context.ofChecked_canReduce, @SignDet.Descriptor.changeOps_raw]

/-- Transport retains the optional canonical cache, with each stored domain
transported to the target operations and no preparation rerun. -/
theorem changeOps_domains (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hg : neg = targetNeg) (hs : sub = targetSub)
    (hm : mul = targetMul) (hi : inv = targetInv) (hd : div = targetDiv)
    (hn : natCast = targetNatCast) (sign : E → Int) (binding : Ctx)
    (context : @Context E Ctx _ _ one add neg sub mul inv div natCast _ sign binding) :
    (@Context.handle E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
      targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context)).map
        (fun h => @SignDet.QueryHandle.domain E Ctx _ _ targetOne targetAdd targetSub targetMul
          targetNatCast targetNeg targetInv _ sign binding _ h) =
    (@Context.handle E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context).map (fun h =>
      @Sturm.PreparedDomain.changeOps E _ _ targetOne targetAdd targetSub targetMul targetNatCast
        targetNeg targetInv one add sub mul natCast neg inv ho ha hs hm hn hg hi
        (@SignDet.QueryHandle.domain E Ctx _ _ one add sub mul natCast neg inv _ sign binding
          (@Context.root E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context) h)) := by
  unfold changeOps
  rw [@Context.ofChecked_domains, Option.map_map]
  congr 1
  funext handle
  dsimp only [Function.comp_def]
  exact @SignDet.QueryHandle.changeOps_domain E Ctx _ _ _ targetOne targetAdd targetSub
    targetMul targetNatCast targetNeg targetInv one add sub mul natCast neg inv
    ho ha hs hm hn hg hi sign binding _ handle

/-- Identity transport preserves the entire immutable context. -/
theorem changeOps_self (sign : E → Int) (binding : Ctx)
    (context : Context E Ctx sign binding) :
    changeOps targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv targetNatCast
      rfl rfl rfl rfl rfl rfl rfl rfl sign binding context = context := by
  unfold changeOps
  dsimp only
  apply Context.ofChecked_context
  · exact SignDet.Descriptor.changeOps_self sign binding context.root
  · exact SignDet.QueryHandle.map_heq context.root _
      (SignDet.Descriptor.changeOps_self sign binding context.root) _
      (SignDet.QueryHandle.changeOps_self sign binding context.root) context.handle

/-- Transport preserves the actual reduction function. -/
theorem changeOps_reduce (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hg : neg = targetNeg) (hs : sub = targetSub)
    (hm : mul = targetMul) (hi : inv = targetInv) (hd : div = targetDiv)
    (hn : natCast = targetNatCast) (sign : E → Int) (binding : Ctx)
    (context : @Context E Ctx _ _ one add neg sub mul inv div natCast _ sign binding) :
    @Context.reduce E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
      targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context) =
    @Context.reduce E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context := by
  cases ho
  cases ha
  cases hg
  cases hs
  cases hm
  cases hi
  cases hd
  cases hn
  rw [changeOps_self]

/-- Transport preserves the actual selected-root sign function. -/
theorem changeOps_signPoly (one : One E) (add : Add E) (neg : Neg E) (sub : Sub E)
    (mul : Mul E) (inv : Inv E) (div : Div E) (natCast : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hg : neg = targetNeg) (hs : sub = targetSub)
    (hm : mul = targetMul) (hi : inv = targetInv) (hd : div = targetDiv)
    (hn : natCast = targetNatCast) (sign : E → Int) (binding : Ctx)
    (context : @Context E Ctx _ _ one add neg sub mul inv div natCast _ sign binding) :
    @Context.signPoly E Ctx _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
      targetNatCast _ sign binding (@changeOps E Ctx _ _ _ targetOne targetAdd targetNeg targetSub targetMul targetInv targetDiv
        targetNatCast one add neg sub mul inv div natCast ho ha hg hs hm hi hd hn
        sign binding context) =
    @Context.signPoly E Ctx _ _ one add neg sub mul inv div natCast _ sign binding context := by
  cases ho
  cases ha
  cases hg
  cases hs
  cases hm
  cases hi
  cases hd
  cases hn
  rw [changeOps_self]

end Hex.RealClosure.Algebraic.Context

/-- info: 'Hex.RealClosure.Algebraic.Context.changeOps_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.changeOps_self
/-- info: 'Hex.RealClosure.Algebraic.Context.changeOps_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.changeOps_reduce
/-- info: 'Hex.RealClosure.Algebraic.Context.changeOps_signPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.changeOps_signPoly

/-- info: 'Hex.RealClosure.Algebraic.Context.changeOps_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Context.changeOps_data
