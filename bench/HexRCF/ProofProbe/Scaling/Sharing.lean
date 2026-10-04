/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Scaling.Degree2
import all HexRCF.ProofProbe.Scaling.Degree2
public import HexRCF.ProofProbe.Scaling.Degree4
import all HexRCF.ProofProbe.Scaling.Degree4
public import HexRCF.ProofProbe.Scaling.Atoms1
import all HexRCF.ProofProbe.Scaling.Atoms1
public import HexRCF.ProofProbe.Scaling.Atoms4
import all HexRCF.ProofProbe.Scaling.Atoms4
public import HexRCF.ProofProbe.Scaling.Bits32
import all HexRCF.ProofProbe.Scaling.Bits32
public import HexRCF.ProofProbe.Scaling.Bits128
import all HexRCF.ProofProbe.Scaling.Bits128
public meta import HexRCF.ProofProbe.Syntax

open Lean Meta

namespace Hex.RCF.ProofProbe.Scaling
run_meta do
  for name in [``Hex.RCF.ProofProbe.Scaling.Degree2.positive,
      ``Hex.RCF.ProofProbe.Scaling.Degree4.positive,
      ``Hex.RCF.ProofProbe.Scaling.Atoms1.positive,
      ``Hex.RCF.ProofProbe.Scaling.Atoms4.positive,
      ``Hex.RCF.ProofProbe.Scaling.Bits32.positive,
      ``Hex.RCF.ProofProbe.Scaling.Bits128.positive] do
    logInfo m!"{(← Hex.RCF.ProofProbe.Syntax.measure name).compress}"
end Hex.RCF.ProofProbe.Scaling
