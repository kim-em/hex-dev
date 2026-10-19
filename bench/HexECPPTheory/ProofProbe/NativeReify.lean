/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPTheory.NativeFixtures

/-! Kernel replay of a complete native output. -/

open Lean Elab Command Meta

run_cmd liftTermElabM do
  let e := Hex.ECPP.reifyCert Hex.ECPP.NativeFixtures.tuning_256_0
  let ty ← inferType e
  unless ty.isConstOf ``Hex.ECPP.Cert do
    throwError "native reification changed the certificate type"
