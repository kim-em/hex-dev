/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Compact
public import HexECPPMathlib.Pari.Process
public meta import HexECPPMathlib.Pari.Process
public import Lean.Elab.Command
public import Lean.Meta.Tactic.TryThis
public import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Proving primality with certificates found by PARI/GP

`primality? (method := pari)` asks the external PARI/GP computer algebra
system to find an elliptic curve primality certificate for the integer in
the goal. Hex completes and converts the data, verifies it in Lean's kernel,
and suggests an `ecpp using` proof containing the saved certificate.

Generation needs the `gp` executable on PATH and a POSIX system. In a batch
build, `#ecpp_export Module.Name cert for n` saves a certificate to a new
Lean module. Checking a saved suggestion or imported certificate never calls
PARI. The external program proposes data; it is not trusted as a proof.
-/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP.Pari

private meta def subject (e : Expr) : MetaM Nat := do
  Hex.PrimalityTactic.checkClosed "PARI" e
  let some n ← getNatValue? (← whnf e)
    | throwError "PARI: expected a closed, transparent natural-number expression"
  unless ← isDefEq e (mkNatLit n) do
    throwError "PARI: subject must be definitionally transparent"
  if HexArith.bitLength n > maxBits then
    throwError "PARI: subject exceeds the {maxBits}-bit replay limit"
  return n

/-- Complete and kernel-check a PARI certificate before publishing any result. -/
meta def generate (n : Nat) : MetaM (String × Cert) := do
  let source ← run n (cancel := (← readThe Core.Context).cancelTk?)
  let cert ← match ← convertSupplied source with
    | .ok cert => pure cert
    | .error err => throwError "PARI conversion: row {err.row}: {repr err.kind}"
  validateCert cert
  let frozen ← match convertText defaultImportBudget source (terminalCert cert) with
    | .ok frozen => pure frozen
    | .error err => throwError "PARI frozen conversion: row {err.row}: {repr err.kind}"
  let proof ← certProof frozen n (mkNatLit n)
  checkWithKernel proof
  return (source, frozen)

/-- Prove the integer in a primality goal using a certificate found by
PARI/GP, and suggest a replacement containing the saved certificate.
Generation requires `gp` on PATH and finite time and output limits.
The resulting proof is kernel-checked; checking the replacement needs no GP. -/
tactic_extension Hex.PrimalityTactic.primalitySuggestTac

@[inherit_doc Hex.PrimalityTactic.primalitySuggestTac,
  tactic_alt Hex.PrimalityTactic.primalitySuggestTac]
syntax (name := pariSuggestTac) "primality?" " (" &"method" " := " &"pari" ")" : tactic

set_option hygiene false in
/-- Prove a closed primality goal using PARI and offer an `ecpp using`
replacement containing the exact checked certificate. -/
@[tactic pariSuggestTac] meta def suggest : Tactic.Tactic := fun stx => do
  let goal ← Tactic.getMainGoal
  goal.withContext <| withOptions (maxRecDepth.set · 65536) do
    let target ← instantiateMVars (← goal.getType)
    let core := target.getAppFn.isConstOf ``Hex.Nat.Prime
    unless (target.getAppFn.isConstOf ``_root_.Nat.Prime || core) && target.getAppNumArgs == 1 do
      throwError "primality? (method := pari): expected a Nat.Prime or Hex.Nat.Prime goal"
    let nE := target.appArg!
    let n ← subject nE
    let (source, cert) ← generate n
    let compact ← compactSyntax source cert
    let replacement ← if core then
      `(tactic| exact Hex.Nat.prime_iff.mpr (by ecpp using ($compact)))
    else `(tactic| ecpp using ($compact))
    let proof ← certProof cert n nE
    let proof ← if core then
      mkAppM ``Iff.mpr #[mkApp (mkConst ``Hex.Nat.prime_iff) nE, proof]
    else pure proof
    goal.assign proof
    Tactic.replaceMainGoal []
    Meta.Tactic.TryThis.addSuggestion stx replacement

/-- Find a primality certificate with PARI/GP and save it in a new Lean
module during `lake build`. For example,
`#ecpp_export MyPrimes.Prime cert for 17` creates `MyPrimes/Prime.lean`.
Remove the command after generation, import that module and use
`ecpp using MyPrimes.Prime.cert`. The proof is kernel-checked before writing;
existing files are never overwritten. -/
syntax (name := pariExportCmd) "#ecpp_export " ident ident " for " term : command

set_option hygiene false in
/-- Run PARI generation for the explicit batch-only exclusive export command. -/
@[command_elab pariExportCmd] meta def exportCert : Command.CommandElab := fun stx => do
  let `(command| #ecpp_export $mod:ident $decl:ident for $term:term) := stx
    | throwUnsupportedSyntax
  exportCertificate mod decl term generate

end Hex.ECPP.Pari
