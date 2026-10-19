/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots

public section

namespace Hex.RealClosure.Tower.Root
variable {registry : BaseContext.Registry} {parent : Context registry}

/-- Insert one root using its existing compatible selected-root comparator,
retaining one representative of roots equal by value. -/
@[expose] def insert (root : Root parent) : List (Root parent) → List (Root parent)
  | [] => [root]
  | next :: rest => match root.compare next with
    | .lt => root :: next :: rest
    | .eq => next :: rest
    | .gt => next :: insert root rest

/-- Order and deduplicate root handles before constructing arithmetic contexts.
Already ascending roots need a linear number of comparisons in reverse traversal;
the worst case of insertion sorting remains quadratic. -/
@[expose] def sort (roots : List (Root parent)) : List (Root parent) :=
  roots.reverse.foldl (fun ordered root => insert root ordered) []

end Hex.RealClosure.Tower.Root
