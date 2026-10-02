/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Soundness
import HexECPP.Import
import HexPrimality.Elab
import Lean.Elab.Tactic

/-!
# Explicit ECPP certificate bridge

`ecpp using c` accepts a closed, exposed data definition. Its body may contain
only certificate, list, and pair constructors and natural-number literals.
The elaborator evaluates that data, reifies it as constructors, and leaves the
checker equation to kernel reduction.
-/

open Lean Elab Meta

namespace Hex.ECPP

/-- Complete a supplied PARI vector using the existing primality elaborator's
endpoint search policy. Conversion remains untrusted; callers pass the
returned raw certificate to `ecpp using` for kernel replay. -/
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
private meta def natType : Expr := mkConst ``Nat

private meta def reifyNats : List Nat → Expr
  | [] => mkApp (mkConst ``List.nil [.zero]) natType
  | x :: xs => mkApp3 (mkConst ``List.cons [.zero]) natType
      (mkNatLit x) (reifyNats xs)

meta def reifyCert : Cert → Expr
  | .base c => mkApp (mkConst ``Hex.ECPP.Cert.base) (Hex.PrimalityTactic.reifyPrimeCert c)
  | .step n a b x y d ws child =>
      mkAppN (mkConst ``Hex.ECPP.Cert.step) #[mkNatLit n, mkNatLit a,
        mkNatLit b, mkNatLit x, mkNatLit y, mkNatLit d,
        reifyNats ws, reifyCert child]

/-- Numeral ceiling admitted by the fresh-module kernel replay probes. -/
def maxBits : Nat := 512
private meta def maxSyntaxNodes : Nat := 131072
private meta def maxInverseWitnesses : Nat := 1024
private meta def maxCertNodes : Nat := 32

private meta def dataConstant (name : Name) : Bool :=
  name == ``Hex.ECPP.Cert || name == ``Hex.Nat.PrimeCert ||
  name == ``Nat || name == ``List || name == ``Prod ||
  name == ``OfNat || name == ``OfNat.ofNat || name == ``OfNat.mk ||
  name == ``instOfNatNat ||
  name == ``Hex.ECPP.Cert.base || name == ``Hex.ECPP.Cert.step ||
  name == ``Hex.Nat.PrimeCert.small || name == ``Hex.Nat.PrimeCert.pock ||
  name == ``Hex.Nat.PrimeCert.pock3 ||
  name == ``Hex.Nat.PrimeCert.pock3Sieve ||
  name == ``List.nil || name == ``List.cons || name == ``Prod.mk

/-- Inspect constructor syntax and exposed data definitions before evaluation.
The shared fuel also bounds nested definitions and list syntax. -/
private meta partial def checkData (e : Expr) (fuel : Nat) : MetaM Nat := do
  if fuel == 0 then throwError "ecpp: certificate syntax exceeds {maxSyntaxNodes} nodes"
  let fuel := fuel - 1
  match e with
  | .app f a => checkData a (← checkData f fuel)
  | .lit (.natVal n) =>
      if HexArith.bitLength n > maxBits then
        throwError "ecpp: a certificate numeral exceeds {maxBits} bits"
      return fuel
  | .const name _ =>
      if dataConstant name then return fuel
      let env ← getEnv
      if (Compiler.getImplementedBy? env name).isSome then
        throwError "ecpp: `{name}` has a compiled implementation; use constructor data"
      unless env.hasExposedBody name do
        throwError "ecpp: `{name}` is not an exposed data definition"
      let some (.defnInfo info) := env.find? name
        | throwError "ecpp: `{name}` is not a data definition"
      try checkData info.value fuel
      catch ex => throwError "ecpp: in exposed `{name}`: {ex.toMessageData}"
  | .mdata _ body => checkData body fuel
  | .letE _ ty val body _ =>
      checkData body (← checkData val (← checkData ty fuel))
  | .bvar _ => return fuel
  | .sort _ => return fuel
  | _ => throwError "ecpp: certificate must be constructor data; got {e}"

private meta partial def countPrimeCert : Hex.Nat.PrimeCert → Nat
  | .small _ => 1
  | .pock _ fs | .pock3 _ _ _ _ fs | .pock3Sieve _ _ _ _ _ fs =>
      1 + (fs.map fun (_, _, c) => countPrimeCert c).sum

private meta def countCert : Cert → Nat
  | .base c => 1 + countPrimeCert c
  | .step _ _ _ _ _ _ _ child => 1 + countCert child

private meta def checkCertBudget : Cert → MetaM Unit
  | .base _ => pure ()
  | .step n _ _ _ _ _ ws child => do
      if HexArith.bitLength n > maxBits then
        throwError "ecpp: certificate subject exceeds {maxBits} bits"
      if ws.length > maxInverseWitnesses then
        throwError "ecpp: inverse transcript exceeds {maxInverseWitnesses} witnesses"
      checkCertBudget child

private meta unsafe def evalCertUnsafe (e : Expr) : MetaM Cert :=
  evalExpr Cert certType e

@[implemented_by evalCertUnsafe]
private meta opaque evalCert (e : Expr) : MetaM Cert

/-- Build a proof from a supplied exposed certificate. The evaluated producer
is discarded; the kernel checks the reified raw data and checker reduction. -/
meta def readCert (e : Expr) : MetaM Cert := do
  Hex.PrimalityTactic.checkClosed "ecpp using" e
  if e.hasSorry then throwError "ecpp: certificate contains an unfinished proof"
  discard <| checkData e maxSyntaxNodes
  let cert ← evalCert e
  if countCert cert > maxCertNodes then
    throwError "ecpp: certificate exceeds {maxCertNodes} total nodes"
  checkCertBudget cert
  unless check cert do
    throwError "ecpp: certificate failed check"
  return cert

/-- Validate a raw proposal against the finite replay policy. -/
meta def validateCert (cert : Cert) : MetaM Unit := do
  discard <| checkData (reifyCert cert) maxSyntaxNodes
  if countCert cert > maxCertNodes then
    throwError "ecpp: certificate exceeds {maxCertNodes} total nodes"
  checkCertBudget cert
  unless check cert do
    throwError "ecpp: certificate failed check"

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
