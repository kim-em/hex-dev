/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.Generated
public meta import KernelReplay.Generated
public import HexRealClosure.PackingReplay
public meta import HexRealClosure.PackingReplay
import all HexSignDet.Codec
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json
import all HexSignDet.Codec.Node
import all HexSignDet.Codec.Evidence
import all HexSignDet.Codec.Value
import all HexSignDet.Descriptor
import all HexRealRoots.TarskiShared
import all HexPoly.Dense
import all HexPoly.Euclid.DivGcd
import all Init.Data.Rat.Basic
import all Init.Data.Array.Basic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.RationalRoot
open Hex.SignDet

/-- Reconstruct a rational selected root from supplied literal graph data.
This reader performs no evidence production. -/
@[expose] def read? (raw : RawDescriptor Rat Nat) (packet : Codec.Json) :
    Option (Descriptor Rat Nat Sturm.orderSign raw.context) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat raw.context
    raw.head raw.lower raw.upper packet).toOption
  let evidence ← graph.replay? Sturm.orderSign raw.context raw.head raw.lower raw.upper raw.queries
  Descriptor.ofReplay? Sturm.orderSign raw.context raw evidence

/-- Base rational coefficient signs are justified by the fixed rational cast,
using only the caller-supplied selected-sign graph. -/
@[expose] def readFact? (context : Context Rat Nat Sturm.orderSign 7)
    (p : DensePoly Rat) (claimed : Int) (packet : Codec.Json) : Option (SignFact context) := do
  let graph ← (Codec.readGraph ValueCodec.rat ValueCodec.nat 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper packet).toOption
  let memo ← graph.validate? Sturm.orderSign 7 context.root.raw.head
    context.root.raw.lower context.root.raw.upper
  context.readSignFact? (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Generated.cast_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) p claimed memo graph.root

public meta section
open Lean Meta Elab Term

/-- Reduce a supplied literal reader, retaining and kernel-checking its
conversion proof before exposing the checked record. -/
def checkedRecord (original : Expr) : MetaM Expr := withExporting (isExporting := false) do
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (whnf original)
  let mut rules : SimpTheorems := {}
  for name in #[``Dag.replay_eq, ``Dag.step_eq, ``Node.check_eq, ``checkMoment_eq,
      ``TarskiCertificate.check_eq, ``Array.toList_range] do
    rules ← rules.addConst name
  rules ← rules.addConst ``Array.all_toList (inv := true)
  rules ← rules.addConst ``Array.foldlM_toList (inv := true)
  let simpContext ← Simp.mkContext (simpTheorems := #[rules])
    (config := { decide := false }) (congrTheorems := ← getSimpCongrTheorems)
  let (simplified, _) ← Meta.simp result simpContext
  let proof ← simplified.getProof' result
  let result ← withOptions (fun options => smartUnfolding.set options false) do
    withTransparency .all (reduce simplified.expr)
  let equation ← mkEq original result
  let _ ← KernelReplay.auditProof proof equation
  KernelReplay.kernelCheck `__rationalRootPacket equation proof
  unless result.getAppFn.isConstOf ``Option.some do
    throwError "literal reader rejected or remained at {result.getAppFn}"
  let record := result.getAppArgs.back!
  let reflexive ← mkEqRefl record
  let _ ← KernelReplay.auditProof reflexive (← inferType reflexive)
  KernelReplay.kernelCheck `__rationalRootRecord (← inferType reflexive) reflexive
  return record

/-- Native production contributes only literal graph data; the returned
term is reconstructed and checked by the ordinary kernel. -/
syntax (name := rationalRoot) "rational_root% " term : term
@[term_elab rationalRoot]
unsafe def elaborateRoot : TermElab := fun stx _ => do
  let rawType ← mkAppM ``RawDescriptor #[mkConst ``Rat, mkConst ``Nat]
  let raw ← Term.withoutErrToSorry (Term.elabTerm stx[1] (some rawType))
  Term.synthesizeSyntheticMVarsNoPostponing
  let raw ← instantiateMVars raw
  let input ← evalExpr (RawDescriptor Rat Nat) (← inferType raw) raw (checkMeta := false)
  let some root := Descriptor.validate Sturm.orderSign input.context input
    | throwError "native rational selected-root production failed"
  let packet := Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode root.evidence)
  checkedRecord (mkApp2 (mkConst ``read?) raw (KernelReplay.jsonExpr packet))

/-- Native scalar production returns only graph data; the fact is reconstructed
and checked from that data in the ordinary kernel. -/
unsafe def produceFact (owner polynomial : Expr) : MetaM Expr := do
  let context ← try
    evalExpr (Context Rat Nat Sturm.orderSign 7) (← inferType owner) owner (checkMeta := false)
    catch error => throwError "scalar context evaluation: {error.toMessageData}"
  let p ← try
    evalExpr (DensePoly Rat) (← inferType polynomial) polynomial (checkMeta := false)
    catch error => throwError "scalar polynomial evaluation: {error.toMessageData}"
  let signs ← match context.buildSigns [context.queryPoly p] with
    | .ok signs => pure signs
    | .error error => throwError "native rational scalar production failed: {reprStr error}"
  let packet := Codec.graph ValueCodec.rat ValueCodec.nat (Dag.encode signs.evidence)
  checkedRecord (← mkAppM ``readFact? #[owner, polynomial, toExpr signs.value,
    KernelReplay.jsonExpr packet])

/-- Supply a base-level scalar fact by producing graph data and independently
reconstructing the fact with the ordinary kernel. -/
syntax (name := rationalFact) "rational_fact% " term "," term : term
@[term_elab rationalFact]
unsafe def elaborateFact : TermElab := fun stx _ => do
  let owner ← Term.withoutErrToSorry (Term.elabTerm stx[1] none)
  let polyType ← mkAppM ``DensePoly #[mkConst ``Rat]
  let polynomial ← Term.withoutErrToSorry (Term.elabTerm stx[3] (some polyType))
  Term.synthesizeSyntheticMVarsNoPostponing
  let owner ← instantiateMVars owner
  let polynomial ← instantiateMVars polynomial
  produceFact owner polynomial

end

end Hex.RealClosure.Algebraic.KernelReplay.RationalRoot
