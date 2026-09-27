/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.ProofProbe.Support

open Lean Elab Command Meta

/-! Construct the production reified certificate without checker replay. -/

syntax "ecpp_reify_probe" : command

elab_rules : command
  | `(ecpp_reify_probe) => do
      let e := Hex.ECPP.reifyCert Hex.ECPP.Fixture65.cert
      let ty ← liftTermElabM <| inferType e
      unless ty.isConstOf ``Hex.ECPP.Cert do
        throwError "ecpp reification changed the certificate type"

ecpp_reify_probe
