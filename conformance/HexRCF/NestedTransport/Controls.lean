/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Read
import HexRCF.NestedTransport.EndpointLiterals
import HexRCF.RealCoefficients
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Controls
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
private def run (source : Descriptor Data.parent.Value Signature Data.parent.sign Data.parent.signature)
    (guards : List Data.parent.Value) (subject graph : Codec.Json) :=
  Hex.RCF.RealCoefficients.NestedTransportTests.Read.readFor Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts
    source guards subject graph
def missingOne := Hex.RCF.RealCoefficients.NestedTransportTests.Read.readAt
  Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts.tail Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts
def missing := Hex.RCF.RealCoefficients.NestedTransportTests.Read.readAt [] Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts
def wrongSource := run Hex.RCF.RealCoefficients.RootTransportConformance.checked.converted []
  Hex.RCF.RealCoefficients.NestedTransportTests.Literals.subject Hex.RCF.RealCoefficients.NestedTransportTests.Literals.graph
def endpointBinding := run Upper.root []
  Hex.RCF.RealCoefficients.NestedTransportTests.EndpointLiterals.subject
  Hex.RCF.RealCoefficients.NestedTransportTests.EndpointLiterals.graph
def zeroGuard := run Upper.root [0] .null .null
private def field (j : Codec.Json) (index : Nat) (replacement : Codec.Json) : Codec.Json :=
  match j with
  | .array values => .arr (values.toArray.set! index replacement)
  | _ => .null
def wrongEndpoint := run Upper.root []
  (field Hex.RCF.RealCoefficients.NestedTransportTests.Literals.subject 2 (.arr #[.number 1,.array .nil])) Hex.RCF.RealCoefficients.NestedTransportTests.Literals.graph
meta section
open Lean Meta Elab Command
elab "#suffix_control " term:term " => " name:ident : command => liftTermElabM do
  let proposition ← Term.elabTerm term (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let decision := mkAppN (mkConst ``Decidable.decide) #[proposition,dictionary]
  let mut rules ← RowTools.rules
  for value in #[``missing, ``missingOne, ``endpointBinding, ``wrongSource, ``zeroGuard, ``wrongEndpoint, ``run,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Read.readFor, ``Hex.RCF.RealCoefficients.NestedTransportTests.Read.readAt,
      ``Hex.RCF.RealCoefficients.RootTransport.readWith, ``Hex.RCF.RealCoefficients.NestedTransportTests.Read.mapped,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.facts, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.first,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.second, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.third,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fourth, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fifth,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.fact, ``Hex.RCF.RealCoefficients.NestedTransportTests.Restore.restore,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.polynomials, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.evidence,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsed, ``Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsedAt, ``Hex.RCF.RealCoefficients.NestedTransportTests.Constants.constant,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.reduce, ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherOne,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherAdd, ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherSub,
      ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherMul, ``Hex.RCF.RealCoefficients.NestedTransportTests.Operations.higherNat] do
    rules ← rules.addDeclToUnfold value
  rules ← rules.addConst ``Hex.RCF.RealCoefficients.NestedTransportTests.Context.signature_eq
  let context ← Simp.mkContext (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[proposition,dictionary,proof]
    KernelCheck.addChecked ((← getCurrNamespace) ++ name.getId) proposition proof
      #[``Descriptor.validate, ``Descriptor.ofReplay?]
  | .checked false .. => throwError "refusal control disagreed"
  | .missing _ => throwError "refusal control needs a scalar record"
end
#suffix_control missingOne.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.evidence => one_missing_record
#suffix_control missing.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.evidence => missing_record
#suffix_control wrongSource.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.binding => wrong_source
#suffix_control endpointBinding.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.binding => endpoint_binding
#suffix_control zeroGuard.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.divisor => zero_before_parse
#suffix_control wrongEndpoint.map (fun _ => ()) = .error Hex.RCF.RealCoefficients.Replay.Error.evidence => changed_endpoint
#suffix_control (Hex.RCF.RealCoefficients.NestedTransportTests.Facts.parsedAt
  (Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts.eraseIdx 13)).isSome = false => missing_predecessor
#print axioms wrong_source
end Hex.RCF.RealCoefficients.NestedTransportTests.Controls
