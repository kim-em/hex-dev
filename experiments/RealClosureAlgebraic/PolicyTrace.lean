/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Policy
open Hex Policy

/-- Untimed call counts from the same callbacks. Modes 4–7 select the same
policies as 0–3 and enable trace output. Preparation precedes each BEGIN. -/
def main : IO Unit := do
  for policy in [:4] do
    let mode := policy+4
    for case in [:10] do
      let n := #[2,3,4,2,3].getD (case/2) 2
      if case < 6 then
        let a := input mode n 0
        let b := input mode (n-1) 1
        let literal := fun (p : DensePoly (Elem (base mode))) =>
          p.toArray.map (fun x => (raw (base mode) x).toArray)
        IO.eprintln s!"PREP,{hash (literal a,literal b)}"
        IO.eprintln s!"BEGIN,{policy},{case}"
        let (q,r) := if case%2 == 0 then DensePoly.divMod a b
          else (DensePoly.monicize (DensePoly.gcd a b),0)
        IO.eprintln s!"END,{hash (q.toArray.map (observe mode),r.toArray.map (observe mode))}"
      else
        let a := nestedInput mode n 0
        let b := nestedInput mode (n-1) 1
        let literal := fun (p : DensePoly (Elem (upper mode))) =>
          p.toArray.map (fun x => (raw (upper mode) x).toArray.map
            (fun y => (raw (base mode) y).toArray))
        IO.eprintln s!"PREP,{hash (literal a,literal b)}"
        IO.eprintln s!"BEGIN,{policy},{case}"
        let (q,r) := if case%2 == 0 then DensePoly.divMod a b
          else (DensePoly.monicize (DensePoly.gcd a b),0)
        IO.eprintln s!"END,{hash (q.toArray.map (observeNested mode),r.toArray.map (observeNested mode))}"
