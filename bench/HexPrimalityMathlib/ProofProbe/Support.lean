/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

/-!
Shared fixed inputs, certificate literals, and the certificate-reification
command for the HexPrimalityMathlib fresh-module proof probes. Measured modules
import this precompiled support module but never import one another.
-/

namespace HexPrimalityMathlib.ProofProbe

open Lean Elab Command Term Meta

syntax "prime31" : term
macro_rules
  | `(prime31) => `(2147483647)

syntax "prime512" : term
macro_rules
  | `(prime512) => `(
      9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177)

syntax "cert31" : term
macro_rules
  | `(cert31) => `(
      Hex.Nat.PrimeCert.pock 2147483647
        [(1745337962, 0, .small 2), (1371693800, 1, .small 3),
         (1615909500, 0, .small 7), (447824900, 0, .small 11),
         (505209180, 0, .small 31), (1783259301, 0, .small 151),
         (904659249, 0, .small 331)])

syntax "cert512" : term
macro_rules
  | `(cert512) => `(
      Hex.Nat.PrimeCert.pock
        9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177
        [(12105408859821572020, 145, .small 2),
         (2427313743710699239, 21,
          .pock 100297
            [(6478, 2, .small 2), (58864, 1, .small 3),
             (35592, 0, .small 7), (37339, 0, .small 199)])])

private meta unsafe def evalCertificateUnsafe (expr : Expr) :
    MetaM (Except String Hex.Nat.PrimeCert) :=
  try
    return .ok (← evalExpr Hex.Nat.PrimeCert
      (mkConst ``Hex.Nat.PrimeCert) expr)
  catch ex =>
    return .error (← ex.toMessageData.toString)

@[implemented_by evalCertificateUnsafe]
private meta opaque evalCertificateCore (expr : Expr) :
    MetaM (Except String Hex.Nat.PrimeCert)

private meta def evalCertificate (expr : Expr) : MetaM Hex.Nat.PrimeCert := do
  match ← evalCertificateCore expr with
  | .ok certificate => return certificate
  | .error msg =>
      throwError "primality proof probe: failed to evaluate certificate\n{msg}"

/-- Elaborate a fixed certificate literal, reify it through the production
certificate reifier, and confirm that the resulting expression is definitionally
equal to the literal. This isolates bridge term construction without rerunning
the core certificate search. -/
syntax "prime_reify_probe " term : command

elab_rules : command
  | `(prime_reify_probe $certificateStx:term) => do
      liftTermElabM do
        let literal ← elabTermEnsuringType certificateStx
          (some (mkConst ``Hex.Nat.PrimeCert))
        synthesizeSyntheticMVarsNoPostponing
        let literal ← instantiateMVars literal
        let certificate ← evalCertificate literal
        let reified := Hex.PrimalityTactic.reifyPrimeCert certificate
        unless ← isDefEq literal reified do
          throwError "primality proof probe: reified certificate changed"

end HexPrimalityMathlib.ProofProbe
