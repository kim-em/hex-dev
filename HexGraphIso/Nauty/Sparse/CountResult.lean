/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountTrace

public section

namespace Hex.GraphIso.Nauty.Sparse.CountTrace

@[expose] def Control.base (s : Control n) (distance : Bool) (first w1 w2 v2 : Nat) : Control n :=
  ((s.hash first).hash (if distance then w2 else w1)).hash v2

@[expose] def Control.pair (s : Control n) (first v2 v3 : Nat) : Control n :=
  if v2 - first <= v3 - v2 && !s.active.mem first then s.push first else s.push v2

/-- The first tail state, after the second fragment has been enqueued and
the initial largest-fragment comparison has executed. -/
@[expose] def Control.more (s : Control n) (distance : Bool) (first v2 v3 : Nat) :
    Control n × Option Nat × Nat :=
  let s := (if distance then s else s.hash v3).push v2
  if v2 - first < v3 - v2 then
    (if distance then s else s.hash (v3 - v2), some (s.queue.size - 1), v3 - v2)
  else (s, none, v2 - first)

/-- The complete control trace of a count split: uniform early return,
two fragments, or the first two fragments followed by the tail derivation. -/
inductive Result {n : Nat} (distance : Bool) (first last : Nat) (s : RefineSt n)
    (lab : Array Nat) : Control n → Prop
  | uniform
      (hu : ∀ q, first ≤ q → q < last → s.hits[s.lab[q]!]! = s.hits[s.lab[first]!]!) :
      Result distance first last s lab ((control s).hash first)
  | divided (hn : ∃ q, first ≤ q ∧ q < last ∧ s.hits[s.lab[q]!]! ≠ s.hits[s.lab[first]!]!)
      (hm : Minima lab s.hits first v2 v3 last w1 w2) (hv : v2 < v3)
      (hc : if v3 = last then out = ((control s).base distance first w1 w2 v2).pair first v2 v3
        else
          let c := ((control s).base distance first w1 w2 v2).more distance first v2 v3
          Tail distance lab s.hits first last (v3 - 1) c.1 c.2.1 c.2.2 out) :
      Result distance first last s lab out

end Hex.GraphIso.Nauty.Sparse.CountTrace
