/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Precision.Bits8
import all HexRCF.ProofProbe.Precision.Bits8
public import HexRCF.ProofProbe.Precision.Bits64
import all HexRCF.ProofProbe.Precision.Bits64
public meta import HexRCF.ProofProbe.Windows.Audit
public meta section

namespace Hex.RCF.ProofProbe.Precision.Audit
run_meta do
  Lean.logInfo m!"{(← Windows.Audit.measure ``Bits8.witness).compress}"
  Lean.logInfo m!"{(← Windows.Audit.measure ``Bits64.witness).compress}"
end Hex.RCF.ProofProbe.Precision.Audit
