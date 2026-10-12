/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.PointReplay
public meta import HexRCF.RealCoefficients.Quote

public meta section
namespace Hex.RCF.RealCoefficients.PointQuote
open Lean Meta

/-- Authenticate and quote an ordinary-point acceptance using the shared
original-source binding and state-restoration boundary. -/
def finish (target original checker accepted valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  Quote.finish ``PointReplay.check ``PointReplay.check_sound 5 false
    target original checker accepted valuationIdentity guardIdentities

end Hex.RCF.RealCoefficients.PointQuote
