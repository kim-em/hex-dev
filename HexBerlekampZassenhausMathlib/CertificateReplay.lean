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

Core's `Array.all` has no exposed body. Its public reduction equation lets
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

end HexBerlekampZassenhausMathlib.CertificateReplay
