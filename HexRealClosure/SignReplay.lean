/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SignFacts
public import HexSignDet.DagOperations

public section

namespace Hex.RealClosure.Algebraic
open SignDet

variable {E Ctx : Type} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}
variable {UpperCtx : Type} [DecidableEq UpperCtx]

/-- Validate every supplied entry with the existing checker and supplied-fact
coefficient operations, then transport its proofs to the ordinary operations.
Missing nonconstant facts block ordinary-kernel reduction at `Element.missing`;
compiled evaluation retains the native fallback. This is a proof-assembly
interface, not a production-free compiled checker. -/
@[expose] def Dag.validateCached? (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (binding : UpperCtx) (head : DensePoly (Element context))
    (lower upper : Endpoint (Element context)) (graph : Dag (Element context) UpperCtx) :
    Option (Array (Dag.Checked Element.sign binding head lower upper)) :=
  @SignDet.Dag.changeOps _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    inferInstance _ (Element.cachedOne reduce hr facts) (Element.cachedAdd reduce hr facts)
    (Element.cachedSub reduce hr facts) (Element.cachedMul reduce hr facts)
    (Element.cachedNatCast reduce hr facts) (Element.cachedOne_eq reduce hr facts)
    (Element.cachedAdd_eq reduce hr facts) (Element.cachedSub_eq reduce hr facts)
    (Element.cachedMul_eq reduce hr facts) (Element.cachedNatCast_eq reduce hr facts)
    Element.sign binding head lower upper
    (@SignDet.Dag.validate? _ _ _ _
      (Element.cachedOne reduce hr facts) (Element.cachedAdd reduce hr facts)
      (Element.cachedSub reduce hr facts) (Element.cachedMul reduce hr facts)
      (Element.cachedNatCast reduce hr facts) _ Element.sign binding head lower upper graph)

/-- Supplied-fact validation preserves exact acceptance, rejection and all
literal checked trees, for every fact list. No completeness premise is hidden. -/
theorem Dag.validateCached_eq (reduce : DensePoly E → DensePoly E)
    (hr : reduce = context.reduce) (facts : List (SignFact context))
    (binding : UpperCtx) (head : DensePoly (Element context))
    (lower upper : Endpoint (Element context)) (graph : Dag (Element context) UpperCtx) :
    Dag.validateCached? reduce hr facts binding head lower upper graph =
      graph.validate? Element.sign binding head lower upper :=
  @SignDet.Dag.changeOps_validate (Element context) UpperCtx _ _
    Element.instOne Element.instAdd Element.instSub Element.instMul Element.instNatCast _
    (Element.cachedOne reduce hr facts) (Element.cachedAdd reduce hr facts)
    (Element.cachedSub reduce hr facts) (Element.cachedMul reduce hr facts)
    (Element.cachedNatCast reduce hr facts) (Element.cachedOne_eq reduce hr facts)
    (Element.cachedAdd_eq reduce hr facts) (Element.cachedSub_eq reduce hr facts)
    (Element.cachedMul_eq reduce hr facts) (Element.cachedNatCast_eq reduce hr facts)
    Element.sign binding head lower upper graph

end Hex.RealClosure.Algebraic

/-- info: 'Hex.RealClosure.Algebraic.Element.cachedInv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.cachedInv_eq
/-- info: 'Hex.RealClosure.Algebraic.Element.cachedDiv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Element.cachedDiv_eq
/-- info: 'Hex.RealClosure.Algebraic.Dag.validateCached_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Dag.validateCached_eq
