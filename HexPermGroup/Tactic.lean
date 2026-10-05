/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Tactic.Replay
public meta import HexPermGroup.Tactic.Replay

public section

/-!
# Permutation-group proof generation

The supported extension interface lives in `Hex.PermGroup.Tactic`.
Certificate representation and replay declarations are implementation details.
-/

namespace Hex.PermGroup.Tactic

export Hex.PermGroup.Kernel.Tactic (Config Input Goal Prepared prepare replay render Extension permGroupTac)

namespace Goal
export Hex.PermGroup.Kernel.Tactic.Goal (card mem notMem all)
end Goal

namespace Prepared
export Hex.PermGroup.Kernel.Tactic.Prepared (order)
end Prepared

end Hex.PermGroup.Tactic
