/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimalityBench.Inputs
public meta import HexPrimalityBench.Inputs

public section

/-!
Shared committed inputs and the compiled-search attribution command for the
core fresh-module probes. Measured modules import this support module but
never one another, so every adjacent pair removes only the intended phase.
-/

namespace Hex.PrimalityProofProbe

open Hex.Nat
open Lean Elab Command Term Meta

inductive Case where
  | bit31
  | bit61
  | bit123
  | bit256
  | bit511
  | bit512
  deriving DecidableEq

private meta def caseOfIdent (caseStx : Syntax) : CommandElabM Case := do
  match caseStx.getId with
  | `bit31 => return .bit31
  | `bit61 => return .bit61
  | `bit123 => return .bit123
  | `bit256 => return .bit256
  | `bit511 => return .bit511
  | `bit512 => return .bit512
  | _ => throwErrorAt caseStx
      "expected one of 'bit31', 'bit61', 'bit123', 'bit256', 'bit511', or 'bit512'"

private meta def Case.subject : Case → Nat
  | .bit31 => primalityInput31
  | .bit61 => primalityInput61
  | .bit123 => primalityInput123
  | .bit256 => primalityInput256
  | .bit511 => primalityInput511
  | .bit512 => primalityInput512

private meta def Case.certificate : Case → PrimeCert
  | .bit31 => primalityCert31
  | .bit61 => primalityCert61
  | .bit123 => primalityCert123
  | .bit256 => primalityCert256
  | .bit511 => primalityCert511
  | .bit512 => primalityCert512

mutual

private meta def certEq : PrimeCert → PrimeCert → Bool
  | .small n, .small m => n == m
  | .pock n xs, .pock m ys => n == m && factorsEq xs ys
  | .pock3 n r s w xs, .pock3 n' r' s' w' ys =>
      n == n' && r == r' && s == s' && w == w' && factorsEq xs ys
  | _, _ => false

private meta def factorsEq : List (Nat × Nat × PrimeCert) →
    List (Nat × Nat × PrimeCert) → Bool
  | [], [] => true
  | (a, e, c) :: xs, (a', e', c') :: ys =>
      a == a' && e == e' && certEq c c' && factorsEq xs ys
  | _, _ => false

end

/-- Run the production elaborator's compiled certificate search, require its
exact committed output, and emit no proof term. -/
syntax "primality_search_probe " ident " : " term : command

elab_rules : command
  | `(primality_search_probe $caseStx:ident : $subjectStx:term) => do
      let case ← caseOfIdent caseStx
      liftTermElabM do
        let subjectExpr ← elabTermEnsuringType subjectStx (some (mkConst ``Nat))
        synthesizeSyntheticMVarsNoPostponing
        let subjectExpr ← instantiateMVars subjectExpr
        let some subject ← getNatValue? subjectExpr
          | throwError "primality proof probe: subject is not a numeral"
        unless subject == case.subject do
          throwError "primality proof probe: subject does not match the fixed case"
        Hex.PrimalityTactic.checkPrimalityPolicy "primality proof probe" subject
        let fuel := Hex.PrimalityTactic.primalityFuel subject
        match Internal.primeCertCountedWith?
            Hex.PrimalityTactic.primalitySearchBudget subject
            (Hex.Rand.ofSeed subject) fuel with
        | .error failure =>
            throwError "primality proof probe: certificate search failed after {failure.attempts} attempts"
        | .ok success =>
            unless success.cert.raw.subject == subject && checkPrime success.cert.raw do
              throwError "primality proof probe: search returned an invalid certificate"
            unless certEq success.cert.raw case.certificate do
              let rendered ← withOptions (fun options =>
                  options.setBool `pp.fullNames true
                    |>.setBool `pp.deepTerms true
                    |>.set `pp.maxSteps (1000000 : Nat)
                    |>.set `format.width (100 : Int)) do
                ppExpr (Hex.PrimalityTactic.reifyPrimeCert success.cert.raw)
              throwError "primality proof probe: emitted certificate literal is stale\n{rendered}"

end Hex.PrimalityProofProbe
