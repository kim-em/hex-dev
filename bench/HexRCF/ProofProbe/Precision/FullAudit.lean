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
public meta section

namespace Hex.RCF.ProofProbe.Precision
open Lean

run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full8.witness).compress}"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full16.witness).compress}"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full32.witness).compress}"
run_meta do
  logInfo m!"{(← Windows.Audit.measure ``Full64.witness).compress}"

end Hex.RCF.ProofProbe.Precision
