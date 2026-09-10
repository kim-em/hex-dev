/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLatticeEnum.Closest

@[expose] public section

namespace Hex.LatticeEnum

/-- Choose a minimum-norm input row; absent exactly at rank zero. -/
def shortestSeed (b : Basis n m) : Option (Point n m) :=
  (List.finRange n).foldl (fun best i =>
    let p := point b 0 (Vector.unit Int i)
    match best with
    | none => some p
    | some q => if p.distanceSq < q.distanceSq then some p else some q) none

/-- Budgeted all-shortest-vector search. Rank zero has no nonzero candidate. -/
def shortestWith (budget : Budget) (b : Basis n m) : Option (Optimization n m) :=
  shortestSeed b |>.map fun seed =>
    (optimize budget b 0 (prepare b 0) .shortest seed).result .shortest

/-- Every shortest nonzero vector, with both signs and all ties retained. -/
def shortest (b : Basis n m) : Option (Minimum n m) :=
  shortestSeed b |>.map fun seed =>
    let run := optimize {} b 0 (prepare b 0) .shortest seed
    ⟨minimumPoints .shortest run.traversal.state.points, run.incumbent.distanceSq⟩

end Hex.LatticeEnum
