/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Trials
public import HexPermGroup.Budget

public section

/-! Compatibility names for the shared producer meter. Search and chain
construction use the same types, so nested producers can retain all counters. -/

namespace Hex.PermGroup.Search

export Hex.PermGroup.Execution (Resource Work Budget Meter Exhausted Measured)

end Hex.PermGroup.Search
