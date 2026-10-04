/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib.Tests.Frozen512

public meta import HexECPPMathlib.Tests.Frozen512

public section

/-! Fresh-module proof phases for the frozen native 512-bit endpoint. -/

open Lean Elab Command Meta

run_cmd liftTermElabM do
  let e := Hex.ECPP.reifyCert Hex.ECPP.Tests.certificate512
  let ty ← inferType e
  unless ty.isConstOf ``Hex.ECPP.Cert do
    throwError "native reification changed the certificate type"
  Hex.ECPP.validateCert Hex.ECPP.Tests.certificate512
