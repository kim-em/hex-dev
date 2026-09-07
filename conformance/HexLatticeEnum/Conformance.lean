/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexLatticeEnum

open Hex Hex.LatticeEnum

namespace Hex.LatticeEnum.Conformance

def matrix (n m : Nat) (rows : List (List Int)) : Matrix Int n m :=
  Matrix.ofFn fun i j => (rows.getD i.val []).getD j.val 0

def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def ball (rows : Matrix Int n m) (target : Vector Rat m) (radius : Rat)
    (expected : List (List Int)) : IO Unit := do
  let some b := ofMatrix? rows | throw (IO.userError "independent fixture rejected")
  let p := prepare b target
  require p.check "invalid native Gram-Schmidt preparation"
  let actual := enumerate b target radius
  require (actual.map (·.ambient.toList) == expected)
    s!"ball mismatch: {repr (actual.map (·.ambient.toList))}"
  require (actual.all (checkPoint b target)) "point reconstruction failed"
  match enumerateWith {} b target radius with
  | .complete points _ counts =>
    require (points == actual) "bounded/unbounded traversal mismatch"
    require (counts.answers == actual.length) "incorrect answer count"
  | .incomplete .. => throw (IO.userError "unlimited search reported incomplete")

def intervals : IO Unit := do
  for u in List.range 23 do
    for v in List.range 5 do
      let c : Rat := ((u : Int) - 11) / ((v + 1 : Nat) : Rat)
      for a in List.range 4 do
        let d : Rat := ((a + 1 : Nat) : Rat) / 3
        for j in List.range 12 do
          let r : Rat := ((j : Int) - 1) / 3
          let s := bounds c d r
          for z0 in List.range 49 do
            let z : Int := (z0 : Int) - 24
            require (decide (s.lo ≤ z ∧ z ≤ s.hi) ==
              decide (d * ((z : Rat) - c) * ((z : Rat) - c) ≤ r))
              s!"incorrect exact interval at {c}, {d}, {r}, {z}"
          let expected := ((List.range s.size).map (fun (k : Nat) => s.lo + (k : Int))).mergeSort
            (fun (x y : Int) => decide (Rat.abs ((x : Rat) - c) < Rat.abs ((y : Rat) - c) ∨
              (Rat.abs ((x : Rat) - c) = Rat.abs ((y : Rat) - c) ∧ x ≤ y)))
          require ((coefficients s c).toList == expected) "coefficient order mismatch"

def budgets : IO Unit := do
  let some b := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]])
    | throw (IO.userError "A2 rejected")
  for limit in [{ nodes := some 0 }, { answers := some 1 }, { certificateNodes := some 1 }] do
    match enumerateWith limit b 0 2 with
    | .complete .. => throw (IO.userError "small budget falsely reported complete")
    | .incomplete ps pending counts =>
      require (!pending.isEmpty) "incomplete result omitted pending work"
      require (ps.all (checkPoint b 0)) "unchecked partial point"
      require (limit.nodes.all (counts.nodes ≤ ·)) "node budget exceeded"
      require (limit.answers.all (counts.answers ≤ ·)) "answer budget exceeded"
      require (limit.certificateNodes.all (counts.certificateNodes ≤ ·))
        "certificate budget exceeded"

def run : IO Unit := do
  intervals
  ball (matrix 2 3 [[1, -1, 0], [0, 1, -1]]) 0 2
    [[-1, 0, 1], [-1, 1, 0], [0, -1, 1], [0, 0, 0], [0, 1, -1], [1, -1, 0], [1, 0, -1]]
  ball (matrix 2 3 [[2, 0, 0], [0, 3, 0]]) #v[1, 3/2, 2] (29/4)
    [[0, 0, 0], [0, 3, 0], [2, 0, 0], [2, 3, 0]]
  ball (matrix 0 2 []) #v[3, 4] 25 [[0, 0]]
  ball (matrix 0 2 []) #v[3, 4] 24 []
  ball (matrix 0 0 []) #v[] 0 [[]]
  ball (matrix 1 1 [[1]]) #v[0] (-1) []
  ball (matrix 1 1 [[1]]) #v[-2001/2] (1/4) [[-1001], [-1000]]
  require (ofMatrix? (matrix 2 2 [[1, 2], [2, 4]])).isNone "dependent basis accepted"
  budgets
  IO.println "lattice enumeration conformance passed"

end Hex.LatticeEnum.Conformance

def main : IO Unit := Hex.LatticeEnum.Conformance.run
