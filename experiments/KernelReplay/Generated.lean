/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SignFacts
public import KernelReplay.ProofProbe
public meta import KernelReplay.ProofProbe
public meta import KernelReplay.Json
public meta import Lean.Meta.Eval
public import HexSignDet.DagEncode
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Value
import all HexRealClosure.Algebraic
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all Init.Data.Array.Basic
import all HexPoly.Euclid.DivGcd

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.Generated
open Lean Meta Elab Command Hex.SignDet
open CoefficientSignsConformance PackingConformance
open scoped Hex

theorem cast_sign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (q : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono q).symm

/-- Proof-assembly helper for the existing rational predecessor fixture.
Only supplied graph data is checked. The fixed interpretation is used in the
proof of the returned fact, not to compute its polynomial or integer sign. -/
@[expose] def factFromJson? (p : DensePoly Rat) (claimed : Int) (j : Codec.Json) :
    Option (SignFact context) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper j).toOption
  let memo ← graph.validate? Sturm.orderSign 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  context.readSignFact? (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) cast_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) p claimed memo graph.root

@[expose] def factFromPackets? (polynomial : Codec.Json) (claimed : Int)
    (graph : Codec.Json) : Option (SignFact context) := do
  let p ← (Codec.readPoly ValueCodec.rat polynomial).toOption
  factFromJson? p claimed graph

meta section

structure Packet where
  polynomial : Codec.Json
  claimed : Int
  graph : Codec.Json

/-- Production may evaluate ordinary coefficients and invoke the existing
prepared BKR producer. Its integer and graph data are then quoted; the fact
itself is assembled and checked using the supplied graph in the kernel. -/
unsafe def produce (needed : KernelReplay.Request) : MetaM (Option Packet) := do
  unless ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) do
    return none
  let key := mkApp (mkConst ``reduction) needed.polynomial
  let normalized ← withTransparency .all (reduce key)
  let expected ← mkAppOptM ``DensePoly #[some (mkConst ``Rat), none, none]
  let p ← evalExpr (DensePoly Rat) expected normalized (checkMeta := false)
  let signs ← match context.buildSigns [context.queryPoly p] with
    | .ok signs => pure signs
    | .error error => throwError "coefficient evidence production failed: {reprStr error}"
  return some ⟨Codec.poly ValueCodec.rat p, signs.value,
    Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode signs.evidence)⟩

/-- Quotation and checking take only supplied literal data. Production is not
called here. Both acceptance and rejection are checked equations for this
particular packet; successful facts are separately audited and kernel checked. -/
def readFact (packet : Packet) : MetaM (Option Expr) := do
  let original := mkAppN (mkConst ``factFromPackets?)
    #[KernelReplay.jsonExpr packet.polynomial, toExpr packet.claimed,
      KernelReplay.jsonExpr packet.graph]
  let result := original
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf result)
  let mut rules : SimpTheorems := {}
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  let equation ← simplified.getProof' result
  let equationType ← mkEq result simplified.expr
  let _ ← KernelReplay.auditProof equation equationType
  KernelReplay.kernelCheck `__kernelReplayGeneratedRead equationType equation
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf simplified.expr)
  unless result.getAppFn.isConstOf ``Option.none || result.getAppFn.isConstOf ``Option.some do
    throwError "supplied coefficient fact did not reduce"
  let converted ← mkAppM ``Eq.trans #[equation, ← mkEqRefl result]
  let conversionType ← mkEq original result
  let _ ← KernelReplay.auditProof converted conversionType
  KernelReplay.kernelCheck `__kernelReplayPacket conversionType converted
  if result.getAppFn.isConstOf ``Option.none then return none
  let fact := result.getAppArgs.back!
  let type ← mkEq fact fact
  let proof ← mkEqRefl fact
  let _ ← KernelReplay.auditProof proof type
  KernelReplay.kernelCheck `__kernelReplayGeneratedFact type proof
  return some fact

/-- Match a demanded retained polynomial against supplied literal packets.
The supplier performs kernel checks and never invokes production. -/
def readPackets (packets : List Packet) (needed : KernelReplay.Request) :
    MetaM (Option Expr) := do
  unless ← isDefEq needed.context (mkConst ``CoefficientSignsConformance.context) do
    return none
  let key := mkApp (mkConst ``reduction) needed.polynomial
  for packet in packets do
    let decoded ← mkAppM ``Codec.readPoly
      #[mkConst ``ValueCodec.rat, KernelReplay.jsonExpr packet.polynomial]
    let decoded ← withTransparency .all (whnf decoded)
    unless decoded.getAppFn.isConstOf ``Except.ok do continue
    let polynomial := decoded.getAppArgs.back!
    let type ← mkEq key polynomial
    let proof ← mkEqRefl polynomial
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let matched := (← getEnv).toKernelEnv.addDecl options
      (.thmDecl { name := `__kernelReplayPacketKey, levelParams := [], type, value := proof })
    if ← KernelReplay.acceptKernel matched then return ← readFact packet
  return none

private def rules : MetaM SimpTheorems := do
  let mut rules : SimpTheorems := {}
  for name in #[``KernelReplayProofProbe.collectionGraph, ``Dag.validateCached?,
      ``Dag.changeOps, ``Dag.validate?, ``Replay.check, ``queryPoly, ``Sturm.check,
      ``SignedRemainderChain.check] do
    rules ← rules.addDeclToUnfold name
  for name in #[``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  rules ← rules.addConst ``eq_self
  rules ← rules.addConst ``iff_self
  return rules

private def replace (j : Codec.Json) (path : List Nat) (expected value : Codec.Json) :
    Option Codec.Json := do
  match path with
  | [] => if j = expected then some value else none
  | i :: rest =>
    let array ← j.getArr?.toOption
    let child ← array[i]?
    let changed ← replace child rest expected value
    return Codec.Json.arr (array.set! i changed)

private unsafe def control : TermElabM Unit := do
  let initial ← Term.withoutErrToSorry
    (Term.elabTerm (← `(([] : List (SignFact context)))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let initial ← instantiateMVars initial
  let context ← Simp.mkContext (simpTheorems := #[← rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let program := mkConst ``KernelReplayProofProbe.collectionGraph
  let packets ← IO.mkRef ([] : List Packet)
  let productionNanos ← IO.mkRef (0 : Nat)
  let readingNanos ← IO.mkRef (0 : Nat)
  let started ← IO.monoNanosNow
  let collected ← KernelReplay.collect 2 program initial context (fun needed => do
    let before ← IO.monoNanosNow
    let some packet ← produce needed | return none
    productionNanos.modify (· + (← IO.monoNanosNow) - before)
    packets.modify (packet :: ·)
    let before ← IO.monoNanosNow
    let some fact ← readFact packet | throwError "generated coefficient evidence was rejected"
    readingNanos.modify (· + (← IO.monoNanosNow) - before)
    return some fact)
  unless collected.requests.size == 2 do
    throwError "unexpected generated fact count: {collected.requests.size}"
  match collected.outcome with
  | .checked true proof axioms =>
    KernelReplay.kernelCheck `__kernelReplayGeneratedGraph
      (← mkEq (mkApp program collected.facts) (mkConst ``Bool.true)) proof
    logInfo m!"generated=2 kernelAccepted=true axioms={axioms} nanos={(← IO.monoNanosNow) - started}"
    logInfo m!"productionNanos={← productionNanos.get} packetCheckNanos={← readingNanos.get}"
  | _ => throwError "fresh coefficient evidence did not complete the actual graph"
  let firstKey ← Term.withoutErrToSorry
    (Term.elabTerm (← `((2 * Sturm.Fixtures.x : DensePoly Rat))) none)
  Term.synthesizeSyntheticMVarsNoPostponing
  let firstKey ← instantiateMVars firstKey
  for (needed, expected) in collected.requests.zip #[firstKey,
      mkConst ``NestedSignsConformance.endpointQuery] do
    let actualContext := mkConst ``CoefficientSignsConformance.context
    KernelReplay.kernelCheck `__kernelReplayGeneratedContext (← mkEq needed.context actualContext)
      (← mkEqRefl actualContext)
    let key := mkApp (mkConst ``reduction) needed.polynomial
    KernelReplay.kernelCheck `__kernelReplayGeneratedKey (← mkEq key expected) (← mkEqRefl expected)
  let packets ← packets.get
  unless packets.length == 2 do throwError "unexpected production call count"
  let replayed ← KernelReplay.collect 2 program initial context (readPackets packets)
  unless replayed.requests.size == 2 do throwError "unexpected packet replay request count"
  match replayed.outcome with
  | .checked true proof _ =>
    KernelReplay.kernelCheck `__kernelReplayPacketGraph
      (← mkEq (mkApp program replayed.facts) (mkConst ``Bool.true)) proof
    logInfo "packetReplay=kernelAccepted"
  | _ => throwError "supplied packets did not replay the actual graph"
  let rejected ← KernelReplay.collect 1 program initial context
    (readPackets (packets.map fun packet => {packet with claimed := -packet.claimed}))
  unless rejected.requests.size == 1 do throwError "unexpected forged packet request count"
  match rejected.outcome with
  | .missing _ => logInfo "forgedPacketReplay=normalRejection"
  | _ => throwError "forged packets established a Boolean result"
  for packet in packets do
    unless (← readFact {packet with claimed := -packet.claimed}).isNone do
      throwError "wrong sign accepted"
  logInfo "generatedWrongSigns=kernelRejected"
  let endpoint := Codec.poly ValueCodec.rat (DensePoly.ofCoeffs #[-1, 2])
  let some packet := packets.find? (·.polynomial == endpoint)
    | throwError "missing endpoint packet"
  let different := Codec.poly ValueCodec.rat Sturm.Fixtures.x
  unless (← readFact {packet with polynomial := different}).isNone do
    throwError "different query accepted"
  logInfo "generatedDifferentQuery=kernelRejected"
  let some stale := replace packet.graph [2, 0, 0, 0] (.number 7) (.number 9)
    | throwError "unexpected generated context layout"
  unless (← readFact {packet with graph := stale}).isNone do
    throwError "stale context accepted"
  logInfo "generatedStaleContext=kernelRejected"
  let some badCount := replace packet.graph [2, 0, 0, 6, 2, 2] (.number 1) (.number 2)
    | throwError "unexpected generated count layout"
  unless (← readFact {packet with graph := badCount}).isNone do
    throwError "forged count accepted"
  logInfo "generatedForgedCount=kernelRejected"

syntax (name := generatedProbe) "#generated_probe" : command
@[command_elab generatedProbe]
unsafe def elaborateGenerated : CommandElab := fun _ => liftTermElabM control

end

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1000000 in
#generated_probe

end Hex.RealClosure.Algebraic.KernelReplay.Generated
