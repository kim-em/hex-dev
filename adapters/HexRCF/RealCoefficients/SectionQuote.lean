/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SectionReplay
public meta import HexRCF.RealCoefficients.Quote

public meta section
namespace Hex.RCF.RealCoefficients.SectionQuote
open Lean Meta

/-- Authenticate and quote a selected-section acceptance using the shared
original-source binding and state-restoration boundary. -/
def finish (target checker accepted valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  Quote.finish ``SectionReplay.check ``SectionReplay.check_sound 8
    target checker accepted valuationIdentity none guardIdentities

end Hex.RCF.RealCoefficients.SectionQuote
