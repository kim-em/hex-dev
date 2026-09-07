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

def minima : IO Unit := do
  let some a2 := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]])
    | throw (IO.userError "A2 rejected")
  let some sv := shortest a2 | throw (IO.userError "positive-rank shortest returned none")
  require (sv.distanceSq == 2 && sv.points.length == 6) "A2 shortest vectors"
  require (sv.points.all fun p => p.ambient != 0 && checkPoint a2 0 p)
    "invalid shortest point"
  let some gap := ofMatrix? (matrix 2 2 [[2, 0], [1, 2]])
    | throw (IO.userError "Babai-gap basis rejected")
  let target := #v[(1 : Rat), 1]
  require ((babai gap target).distanceSq == 2) "unexpected nearest-plane candidate"
  let cv := closest gap target
  require (cv.distanceSq == 1 && cv.points.map (·.ambient.toList) == [[1, 2]])
    "closest search failed to improve Babai"
  match closestWith { certificateNodes := some 0 } gap target with
  | .complete .. => throw (IO.userError "uncertified optimum claimed complete")
  | .incomplete incumbent _ pending phase _ =>
    require (incumbent.distanceSq == 1 && phase == .ties && !pending.isEmpty)
      "tie pass did not retain the improved incumbent"
  let some square := ofMatrix? (matrix 2 2 [[1, 0], [0, 1]])
    | throw (IO.userError "square basis rejected")
  let ties := closest square #v[1/2, 1/2]
  require (ties.distanceSq == 1/2 && ties.points.map (·.ambient.toList) ==
    [[0, 0], [0, 1], [1, 0], [1, 1]]) "closest ties missing"
  let some zero := ofMatrix? (matrix 0 2 []) | throw (IO.userError "rank zero rejected")
  require (shortest zero).isNone "rank-zero shortest is not none"
  let cv0 := closest zero #v[3, 4]
  require (cv0.distanceSq == 25 && cv0.points.map (·.ambient.toList) == [[0, 0]])
    "rank-zero closest failed"

def certificates : IO Unit := do
  let some b := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]])
    | throw (IO.userError "A2 rejected")
  let cert := enumerationCertificate b 0 2
  require (checkEnumeration b 0 2 cert) "native certificate rejected"
  require (!checkEnumerationWith (cert.tree.nodes - 1) b 0 2 cert)
    "replay node budget not enforced"
  require (!checkEnumeration b 0 2 { cert with forward := 0 }) "corrupt transform accepted"
  let badData := { cert.data with norms := #v[(0 : Rat), 1] }
  require (!checkEnumeration b 0 2 { cert with data := badData }) "corrupt norms accepted"
  require (!checkEnumeration b 0 2 { cert with points := cert.points.drop 1 })
    "missing claimed point accepted"
  match cert.tree with
  | .node interval children =>
    require (!checkEnumeration b 0 2
      { cert with tree := .node ⟨interval.lo, interval.hi + 1⟩ children })
      "corrupt endpoint accepted"
    require (!checkEnumeration b 0 2
      { cert with tree := .node interval (children.drop 1) }) "missing branch accepted"
    require (!checkEnumeration b 0 2
      { cert with tree := .node interval (children ++ children.take 1) })
      "duplicate branch accepted"
    match children with
    | (a, .node inner ((c, _) :: tail)) :: rest =>
      let corrupt := Tree.node interval ((a, .node inner ((c, .empty) :: tail)) :: rest)
      require (!checkEnumeration b 0 2 { cert with tree := corrupt }) "missing leaf accepted"
    | _ => throw (IO.userError "unexpected A2 tree")
  | _ => throw (IO.userError "missing A2 tree")
  let some sv := shortest b | throw (IO.userError "missing shortest result")
  let some candidate := sv.points.head? | throw (IO.userError "missing shortest point")
  require (checkShortest b ⟨candidate, cert⟩) "shortest certificate rejected"
  let u := matrix 2 2 [[-1, 0], [0, 1]]
  let some changed := ofMatrix? (u * b.rows) | throw (IO.userError "changed basis rejected")
  let other := enumerationCertificate changed 0 2
  let transported : Certificate 2 3 :=
    { other with
      forward := u
      reverse := u
      points := other.points.map fun p => point b 0 (u.transpose * p.coefficients) }
  require (checkEnumeration b 0 2 transported) "determinant-minus-one transform rejected"
  require (transported.points == cert.points) "original coefficient reconstruction disagrees"

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
  minima
  certificates
  IO.println "lattice enumeration conformance passed"

end Hex.LatticeEnum.Conformance

def main : IO Unit := Hex.LatticeEnum.Conformance.run
