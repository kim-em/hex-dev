/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import KernelReplay.ProofAudit
public meta import KernelReplay.AxiomClosure

public meta section
open Lean Meta Elab
open Hex.RealClosure.Algebraic.KernelReplay

-- A module import retains a hidden definition as a placeholder. It must not
-- pass the fixed whitelist when its original body is unavailable.
set_option maxHeartbeats 2000000 in
run_meta do
  let rejected ← try
    let _ ← AxiomClosure.audit (mkConst ``ProofAudit.index) (mkConst ``Nat)
    pure false
  catch error =>
    unless (← error.toMessageData.toString).startsWith
        "unapproved dependency (axiom or hidden body):" do throw error
    pure true
  unless rejected do
    throwError "dependency audit accepted an unavailable imported body"
