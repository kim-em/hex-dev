/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.InProcessProbe
public import KernelReplay.LowerProbe
public import HexRealClosureMathlib.NestedSignsConformance
public import HexSignDet.DagEncode
import all HexRealClosure.Algebraic
import all HexPoly.Euclid.DivGcd
import all HexSignDet.Descriptor

public section

open Hex Hex.RealClosure.Algebraic
open CoefficientSignsConformance PackingConformance NestedSignsConformance InProcessProbe
open Hex.SignDet Hex.SignDet.Conformance
open scoped Hex

@[expose] def lowerGraph : Dag Rat Nat := ⟨#[⟨endpointNode, none⟩], 0⟩

@[expose] def lowerEval (graph : Dag Rat Nat) (claimed : Int) (index : Nat := 0) : Option Int := do
  let memo ← graph.validate? Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
  LowerProbe.readEvalSign? linearHead (rational 1) claimed memo index

set_option maxRecDepth 32768 in
example : reduction (LowerProbe.evalPolynomial linearHead (rational 1)) = endpointQuery := by
  decide +kernel

@[expose] def lowerMemo : Array (Dag.Checked Sturm.orderSign 7
    singletonRaw.head singletonRaw.lower singletonRaw.upper) :=
  #[⟨.leaf endpointNode, by
    have h := endpoint_checked
    simp only [Descriptor.checkSigns, CoefficientSignsConformance.source_raw,
      RawDescriptor.checkSigns, Bool.and_eq_true] at h
    exact h.1.2⟩]

set_option maxRecDepth 32768 in
theorem lower_query : context.queryPoly (LowerProbe.evalPolynomial linearHead (rational 1)) =
    endpointQuery := by
  simp only [Context.queryPoly, Context.queryRemainder, context, Context.root_adjoin,
    CoefficientSignsConformance.source_raw, singletonRaw, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
example : LowerProbe.readEvalSign? linearHead (rational 1) 1 lowerMemo 0 = some 1 := by
  simp only [LowerProbe.readEvalSign?, Context.readSigns?]
  rw [lower_query]
  decide +kernel

set_option maxRecDepth 32768 in
example : LowerProbe.readEvalSign? linearHead (rational 1) (-1) lowerMemo 0 = none ∧
    LowerProbe.readEvalSign? linearHead (rational 1) 1
      (#[] : Array (Dag.Checked Sturm.orderSign 7 singletonRaw.head singletonRaw.lower
        singletonRaw.upper)) 0 = none := by
  constructor <;>
    simp only [LowerProbe.readEvalSign?, Context.readSigns?] <;>
    rw [lower_query] <;>
    decide +kernel

@[expose] def zeroMoment : TarskiCertificate Rat Rat Nat :=
  {singletonQuery with
    queryPoly := 0
    remainders := {
      chain := #[Sturm.Fixtures.p]
      degrees := #[2]
      initial := ⟨1, 0, 1⟩
      steps := #[]
      terminal := none}
    lowerSigns := #[-1]
    upperSigns := #[1]
    lowerVariations := 0
    upperVariations := 0
    value := 0}

@[expose] def zeroNode : Node Rat Nat :=
  {selectedNode with
    queries := [0]
    system := {selectedNode.system with counts := #v[0, 1, 0], values := #v[1, 0, 0]}
    moments := #v[singletonQuery, zeroMoment, zeroMoment]}

set_option maxRecDepth 32768 in
theorem zero_checked : source.checkSigns [0] #v[0] (.leaf zeroNode) = true := by
  simp only [Descriptor.checkSigns, CoefficientSignsConformance.source_raw,
    RawDescriptor.checkSigns, Replay.check, Node.check_eq, checkMoment_eq, queryPoly,
    Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def zeroMemo : Array (Dag.Checked Sturm.orderSign 7
    singletonRaw.head singletonRaw.lower singletonRaw.upper) :=
  #[⟨.leaf zeroNode, by
    have h := zero_checked
    simp only [Descriptor.checkSigns, CoefficientSignsConformance.source_raw,
      RawDescriptor.checkSigns, Bool.and_eq_true] at h
    exact h.1.2⟩]

set_option maxRecDepth 32768 in
theorem difference_query : context.queryPoly (literal.polynomial - small.polynomial) = 0 := by
  simp only [Context.queryPoly, Context.queryRemainder, context, Context.root_adjoin,
    CoefficientSignsConformance.source_raw, singletonRaw, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
example : literal.polynomial ≠ small.polynomial ∧
    LowerProbe.readDifferenceSign? literal small 0 zeroMemo 0 = some 0 := by
  constructor
  · decide +kernel
  · simp only [LowerProbe.readDifferenceSign?, Context.readSigns?]
    rw [difference_query]
    decide +kernel

@[expose] def endpoints (facts : List (SignFact context)) : Option Bool :=
  (readEndpoints? reduction reduction_eq facts linearHead linearRaw.lower linearRaw.upper).map (·.val)

set_option maxRecDepth 32768 in
example : endpoints NestedSignsConformance.facts = some true := by decide +kernel

set_option maxRecDepth 32768 in
example : endpoints PackingConformance.facts = none := by decide +kernel

set_option maxRecDepth 32768 in
example : readEval? reduction reduction_eq PackingConformance.facts linearHead (rational 1) = none := by
  decide +kernel

/-- info: 'Hex.RealClosure.Algebraic.InProcessProbe.readEndpoints?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.InProcessProbe.readEndpoints?

private def expect (label : String) (actual expected : Option Bool) : IO Unit := do
  if actual != expected then
    throw (IO.userError s!"{label}: got {actual}, expected {expected}")
  IO.println s!"{label}: passed"

def main : IO UInt32 := do
  expect "lower-memo-missing" ((lowerEval ⟨#[], 0⟩ 1).map (· == 1)) none
  expect "lower-memo-complete" ((lowerEval lowerGraph 1).map (· == 1)) (some true)
  expect "lower-memo-wrong-sign" ((lowerEval lowerGraph (-1)).map (· == 1)) none
  expect "lower-memo-missing-index" ((lowerEval lowerGraph 1 1).map (· == 1)) none
  expect "lower-memo-stale-context"
    ((lowerEval (Dag.encode (.leaf {endpointNode with context := 8})) 1).map (· == 1)) none
  expect "lower-memo-wrong-query"
    ((lowerEval (Dag.encode (.leaf firstNode)) 1).map (· == 1)) none
  expect "different-representatives-zero-difference"
    ((LowerProbe.readDifferenceSign? literal small 0 zeroMemo 0).map (· == 0)) (some true)
  expect "zero-difference-missing"
    ((LowerProbe.readDifferenceSign? literal small 0
      (#[] : Array (Dag.Checked Sturm.orderSign 7 singletonRaw.head singletonRaw.lower
        singletonRaw.upper)) 0).map (· == 0)) none
  expect "zero-difference-wrong-sign"
    ((LowerProbe.readDifferenceSign? literal small 1 zeroMemo 0).map (· == 0)) none
  expect "missing-endpoint-fact" (endpoints PackingConformance.facts) none
  expect "complete-after-missing" (endpoints NestedSignsConformance.facts) (some true)
  expect "missing-Horner-fact"
    ((readEval? reduction reduction_eq PackingConformance.facts linearHead (rational 1)).map
      (fun a => a.sign == 1)) none
  expect "complete-Horner"
    ((readEval? reduction reduction_eq NestedSignsConformance.facts linearHead (rational 1)).map
      (fun a => a.sign == 1)) (some true)
  expect "zero-head"
    ((readEndpoints? reduction reduction_eq ([] : List (SignFact context)) 0
      linearRaw.lower linearRaw.upper).map (·.val)) (some false)
  expect "reversed-interval"
    ((readEndpoints? reduction reduction_eq ([] : List (SignFact context)) linearHead
      linearRaw.upper linearRaw.lower).map (·.val)) (some false)
  expect "infinite-interval"
    ((readEndpoints? reduction reduction_eq ([] : List (SignFact context)) linearHead
      .negInf .posInf).map (·.val)) (some true)
  expect "constant-result"
    ((readValue? reduction reduction_eq ([] : List (SignFact context)) (DensePoly.C (3 : Rat))).map
      (fun a => a.sign == 1)) (some true)
  expect "canonical-zero"
    ((readValue? reduction reduction_eq ([] : List (SignFact context)) 0).map
      (fun a => a == 0)) (some true)
  expect "missing-literal-result"
    ((readValue? reduction reduction_eq ([] : List (SignFact context))
      (2 * Sturm.Fixtures.x)).map (fun a => a.sign == 1)) none
  expect "complete-after-second-missing" (endpoints NestedSignsConformance.facts) (some true)
  return 0
