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
import all HexRCF.ProofProbe.Windows.Audit
public meta section

namespace Hex.RCF.ProofProbe.Precision
open Lean Meta

private def hasWindow (name : Name) : MetaM Bool := do
  let some owner := (← getEnv).getModuleIdxFor? name | throwError "proof is not imported"
  let (_, counts) ← (Windows.Audit.declaration owner name).run {}
  return counts.expressions.toList.any fun (e, _) =>
    e.isConstOf ``Hex.RCF.RealCoefficients.LiteralSign.Window.mk

-- The imported-proof traversal must observe a known positive window control.
run_meta do
  unless ← hasWindow ``Windows.FixedRefined.witness do
    throwError "imported window control was not observed"

run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full8.witness).compress}"
  if ← hasWindow ``Full8.witness then
    throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full16.witness).compress}"
  if ← hasWindow ``Full16.witness then
    throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full32.witness).compress}"
  if ← hasWindow ``Full32.witness then
    throwError "initial precision arm unexpectedly refined its generator"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full64.witness).compress}"
  if ← hasWindow ``Full64.witness then
    throwError "initial precision arm unexpectedly refined its generator"

end Hex.RCF.ProofProbe.Precision
