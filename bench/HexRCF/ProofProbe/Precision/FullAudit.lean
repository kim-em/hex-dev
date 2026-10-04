/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Precision.Full8
import all HexRCF.ProofProbe.Precision.Full8
public import HexRCF.ProofProbe.Precision.Full16
import all HexRCF.ProofProbe.Precision.Full16
public import HexRCF.ProofProbe.Precision.Full32
import all HexRCF.ProofProbe.Precision.Full32
public import HexRCF.ProofProbe.Precision.Full64
import all HexRCF.ProofProbe.Precision.Full64
public meta import HexRCF.ProofProbe.Windows.Audit
public meta import HexRCF.ProofProbe.Literals.Support
public meta section

namespace Hex.RCF.ProofProbe.Precision
open Lean

run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full8.witness).compress}"
  let window ← Literals.usesConstructor ``Full8.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full16.witness).compress}"
  let window ← Literals.usesConstructor ``Full16.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full32.witness).compress}"
  let window ← Literals.usesConstructor ``Full32.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full64.witness).compress}"
  let window ← Literals.usesConstructor ``Full64.witness
    ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk 0
  unless window == false do throwError "initial precision arm unexpectedly refined its generator"

end Hex.RCF.ProofProbe.Precision
