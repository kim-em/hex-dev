/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.CertificationInputs
public import HexRCF.RealCoefficients
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
namespace Hex.RCF.SuppliedBudget

-- This quartic has an existing certificate producer; exhaustion must not use it.
abbrev polynomial : ZPoly := DensePoly.ofCoeffs #[-2, -7, -1, 4, 1]

-- There is deliberately no base instance: resolving this premise consumes the budget.
class SearchTag (n : Nat) : Prop where
  valid : True
private instance {n : Nat} [SearchTag (n + 1)] : SearchTag n := ⟨True.intro⟩

namespace Divergent
scoped instance proposed [SearchTag 0] : polynomial.CheckedIrreducible := by
  change CertificationInputs.polynomial.CheckedIrreducible
  exact CertificationInputs.checked
end Divergent

/-- info: 'Hex.RCF.SuppliedBudget.Divergent.proposed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Divergent.proposed

namespace Failure
open scoped Divergent
run_meta do
  let p : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let saved ← saveState
  let rejected ← try
    let _ ← withOptions (fun options => synthInstance.maxHeartbeats.set options 1)
      (CommonTactic.certify p expression degree)
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  let some message := rejected | throwError "instance search exhaustion fell through to a certificate producer"
  unless (message.splitOn "synthInstance.maxHeartbeats").length > 1 &&
      message.startsWith "failed to synthesize" &&
      (message.splitOn "CheckedIrreducible").length > 1 do
    throwError "unexpected instance-search failure: {message}"
end Failure

-- The scoped instance is absent here, and the ordinary producer remains usable.
run_meta do
  let p : ZPoly := DensePoly.ofList [-2, -7, -1, 4, 1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let target ← mkAppM ``ZPoly.CheckedIrreducible #[expression]
  unless (← withOptions (fun options => synthInstance.maxHeartbeats.set options 1)
      (synthInstance? target)).isNone do
    throwError "exhausting supplied instance escaped its scope"
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let checked ← CommonTactic.certify p expression degree
  Hex.RCF.checkAxioms `Hex.RCF.SuppliedBudget.normal checked
end Hex.RCF.SuppliedBudget
