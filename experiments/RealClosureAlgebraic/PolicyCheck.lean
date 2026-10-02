/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Policy
import Lean.Data.Json
open Hex Policy Lean

def emit (xs : List (String × Json)) : IO Unit := IO.println (Json.mkObj xs).compress
def jsonValue (xs : Array Rat) : Json := toJson (xs.map toString)
def jsonPoly (mode : Nat) (p : DensePoly (Elem (base mode))) : Json :=
  Json.arr (p.toArray.map (jsonValue ∘ observe mode))
def jsonNested (mode : Nat) (p : DensePoly (Elem (upper mode))) : Json :=
  Json.arr (p.toArray.map fun a => Json.arr ((observeNested mode a).map jsonValue))

def main : IO Unit := do
  for mode in [:4] do
    for n in [2,3,4] do
      let a := input mode n 0
      let b := input mode (n-1) 1
      let (q,r) := DensePoly.divMod a b
      let g := DensePoly.monicize (DensePoly.gcd a b)
      emit [("kind",toJson "base"),("mode",toJson mode),("n",toJson n),
        ("a",jsonPoly mode a),("b",jsonPoly mode b),("q",jsonPoly mode q),
        ("r",jsonPoly mode r),("g",jsonPoly mode g),
        ("maxStored",toJson ((q.toArray++r.toArray++g.toArray).foldl
          (fun n a => max n (raw (base mode) a).natDegree) 0))]
    for n in [2,3] do
      let a := nestedInput mode n 0
      let b := nestedInput mode (n-1) 1
      let (q,r) := DensePoly.divMod a b
      let g := DensePoly.monicize (DensePoly.gcd a b)
      let ds := (q.toArray++r.toArray++g.toArray).foldl
        (fun ds a => let d := degrees mode a; (max ds.1 d.1,max ds.2 d.2)) (0,0)
      emit [("kind",toJson "nested"),("mode",toJson mode),("n",toJson n),
        ("a",jsonNested mode a),("b",jsonNested mode b),("q",jsonNested mode q),
        ("r",jsonNested mode r),("g",jsonNested mode g),
        ("maxStored",toJson #[ds.1,ds.2])]
    let mut power := pack (base mode) (DensePoly.monomial 1 1)
    for step in [:7] do
      emit [("kind",toJson "growth"),("mode",toJson mode),("step",toJson step),
        ("storedDegree",toJson (raw (base mode) power).natDegree),
        ("value",jsonValue (observe mode power))]
      power := power*power
