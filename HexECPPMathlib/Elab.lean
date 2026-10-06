/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Soundness
public import HexECPP.ElabData
public import HexECPP.Import
public meta import HexECPP.Import
public import HexECPPMathlib.Policy
public meta import HexECPPMathlib.Policy
public import HexPrimality.Elab
public import Lean.Elab.Tactic

/-!
# Lean proofs from supplied primality certificates

`ecpp using c` proves `Nat.Prime n` by checking a supplied elliptic curve
primality certificate for `n` and applying the proved soundness theorem.
The certificate is saved mathematical data; this tactic does not search for
curves or call PARI.

Saved definitions must expose their bodies and contain only certificate,
list and pair constructors, natural-number literals, and data let bindings.
Local hypotheses and executable search calls are not certificate data.
After reading the data, the elaborator constructs a literal certificate
expression and leaves the checker equation to Lean's kernel.
-/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP

/-- Convert PARI certificate text while searching for a proof of the last
prime in its chain. The search uses the existing primality elaborator's
finite policy. To obtain a Lean theorem, the returned certificate must still
be passed to `ecpp using`, which verifies it in the kernel. -/
meta def convertSupplied (source : String) : MetaM (Except ImportError Cert) := do
  let parsed ← match parsePari defaultImportBudget source with
    | .ok input => pure input
    | .error kind => return .error { row := 0, kind := kind }
  let endpoint := parsed.endpoint
  unless Hex.PrimalityTactic.withinPrimalityBudget endpoint do
    return .error { row := parsed.rows.length, kind := .exhausted }
  let fuel := min (Hex.PrimalityTactic.primalityFuel endpoint)
    defaultImportBudget.maxEndpointFuel
  return (convertCounted defaultImportBudget Hex.PrimalityTactic.primalitySearchBudget
    (Hex.Rand.ofSeed endpoint) fuel parsed).map Prod.fst

private meta def certType : Expr := mkConst ``Hex.ECPP.Cert

/-- Produce the subject-bound proof from checked raw constructor data. -/
meta def certProof (cert : Cert) (n : Nat) (nE : Expr) : MetaM Expr := do
  validateCert cert
  unless cert.subject == n do
    throwError "ecpp: certificate subject is {cert.subject}; expected {n}"
  unless checkAt n cert do
    throwError "ecpp: certificate for {n} failed checkAt"
  return mkApp3 (mkConst ``Hex.ECPP.natPrime_of_checkAt) nE
    (reifyCert cert) Hex.PrimalityTactic.reflTrue

private meta def proveUsing (stx : Term) (n : Nat) (nE : Expr) : Term.TermElabM Expr := do
  withOptions (maxRecDepth.set · 65536) do
    let e ← Term.withoutErrToSorry do
      Term.elabTermEnsuringType stx certType
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    certProof (← readCert e) n nE

/-- Produce `Nat.Prime n` from an explicit, checked ECPP certificate. -/
syntax (name := ecppUsingTac) "ecpp" " using " term : tactic

/-- Elaborate explicit certificate replay for a closed Mathlib primality goal. -/
@[tactic ecppUsingTac] meta def evalEcppUsing : Tactic.Tactic := fun stx => do
  match stx with
  | `(tactic| ecpp using $source) => do
      let goal ← Tactic.getMainGoal
      let proof ← Tactic.withMainContext do
        let target ← instantiateMVars (← goal.getType)
        unless target.getAppFn.isConstOf `Nat.Prime &&
            target.getAppNumArgs == 1 do
          throwError "ecpp: expected a `Nat.Prime n` goal, got {target.getAppFn.constName!}{indentExpr target}"
        let nE := target.appArg!
        Hex.PrimalityTactic.checkClosed "ecpp" nE
        let some n ← getNatValue? (← whnf nE)
          | throwError "ecpp: goal subject is not a natural-number numeral"
        unless ← isDefEq nE (mkNatLit n) do
          throwError "ecpp: subject must be definitionally transparent"
        if HexArith.bitLength n > maxBits then
          throwError "ecpp: subject exceeds the measured {maxBits}-bit replay limit"
        proveUsing source n nE
      goal.assign proof
      Tactic.replaceMainGoal []
  | _ => Elab.throwUnsupportedSyntax

end Hex.ECPP
