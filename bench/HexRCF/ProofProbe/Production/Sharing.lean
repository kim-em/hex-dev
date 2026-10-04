/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Production.Close
public import HexRCF.ProofProbe.Production.Further
import all HexRCF.ProofProbe.Production.Close
import all HexRCF.ProofProbe.Production.Further
public meta import HexRCF.ProofProbe.Syntax

/-! Deterministic syntax accounting for actual quoted proofs. Count all reachable
declaration types and bodies emitted in the proof's module, including auxiliary
check theorems. Imported library declarations remain constant references.

Local expression tree nodes expand structural syntax sharing in each local
declaration type and body once, treating
constants as leaves. Unique nodes use structural expression equality. Universe
levels and binder names are not separate nodes. Expanded work substitutes the
local declaration type and body at every reference, with memoized counting.
Neither count is a runtime estimate or a physical heap-sharing measurement. -/

namespace Hex.RCF.ProofProbe.Production.Sharing
open Lean Meta

run_meta do
  for name in [``Hex.RCF.ProofProbe.Production.closeSections,
      ``Hex.RCF.ProofProbe.Production.furtherSection] do
    logInfo m!"{(← Hex.RCF.ProofProbe.Syntax.measure name).compress}"

end Hex.RCF.ProofProbe.Production.Sharing
