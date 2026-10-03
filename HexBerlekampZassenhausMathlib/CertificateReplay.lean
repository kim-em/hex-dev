/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.FactorTransport
public meta import Lean.Meta.Tactic.Cbv

public section

/-!
Literal multi-prime certificate replay under ordinary public imports.

Importing this module registers `Array.all_eq_not_any_not` globally as a
`cbv_eval` equation. Core's `Array.all` has no exposed body. Its public
reduction equation lets
`cbv` evaluate it with a kernel-checked proof instead. The other checker
operations use their exposed bodies or public recursion equations; replay
never evaluates the certificate search or the integer factorizer.
-/

attribute [cbv_eval] Array.all_eq_not_any_not

namespace HexBerlekampZassenhausMathlib.CertificateReplay

open Lean Meta

/-- Prove a literal Boolean certificate check by theorem-backed evaluation.
Returns an ordinary kernel proof of `check = true`, rejecting false or stuck
checks. The caller supplies the existing checker applied to reified data. -/
meta def checkProof (check : Expr) : MetaM Expr := do
  let goal ← mkFreshExprMVar (← mkEq check (mkConst ``Bool.true))
  Lean.Meta.Tactic.Cbv.cbvDecideGoal goal.mvarId!
  instantiateMVars goal

/-- Assemble the existing cover checker from its three Boolean checks.
Only the multi-prime check needs theorem-backed evaluation; the free witness
and coefficientwise membership checks retain direct kernel reduction. -/
theorem checkCover (factors : List Hex.ZPoly)
    (certified : List (Hex.ZPoly × Hex.ZPoly.IrredWitness))
    (multiPrime : List (Hex.ZPoly × Hex.ZPolyIrreducibilityCertificate))
    (hcert : (certified.all fun e => Hex.ZPoly.checkIrredWitness e.1 e.2) = true)
    (hmulti : (multiPrime.all fun e => checkMultiPrimeCert e.1 e.2) = true)
    (hcover : (factors.all fun q =>
      (certified.any fun e => Hex.DensePoly.beqCoeffs e.1 q) ||
        (multiPrime.any fun e => Hex.DensePoly.beqCoeffs e.1 q)) = true) :
    checkMultiPrimeCover factors certified multiPrime = true := by
  simp only [checkMultiPrimeCover, Bool.and_eq_true]
  exact ⟨⟨hcert, hmulti⟩, hcover⟩

end HexBerlekampZassenhausMathlib.CertificateReplay
