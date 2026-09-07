/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexLatticeEnum

/-!
Oracle: independent Python integer/Fraction Cartesian enumeration.
Mode: always.
Covered operations: preparation, exact bounds, coefficient ordering, ball enumeration,
Babai, shortest and closest vectors, all three budgets, and certificate replay.
Covered properties: closed-ball membership, reconstruction, all ties, resource limits,
rejection of forged optimality and malformed exhaustive trees, and basis transport.
Covered edge cases: empty rank and ambient dimension, rectangular bases, off-span targets,
negative and zero radii, half-integer centres, dependent rows, and negative coefficients.
-/

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
  require (actual.all (checkPoint b.rows target)) "point reconstruction failed"
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
      require (ps.all (checkPoint b.rows 0)) "unchecked partial point"
      require (limit.nodes.all (counts.nodes ≤ ·)) "node budget exceeded"
      require (limit.answers.all (counts.answers ≤ ·)) "answer budget exceeded"
      require (limit.certificateNodes.all (counts.certificateNodes ≤ ·))
        "certificate budget exceeded"

def minima : IO Unit := do
  let some a2 := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]])
    | throw (IO.userError "A2 rejected")
  let some sv := shortest a2 | throw (IO.userError "positive-rank shortest returned none")
  require (sv.distanceSq == 2 && sv.points.length == 6) "A2 shortest vectors"
  require (sv.points.all fun p => p.ambient != 0 && checkPoint a2.rows 0 p)
    "invalid shortest point"
  let some gap := ofMatrix? (matrix 2 2 [[2, 0], [1, 2]])
    | throw (IO.userError "Babai-gap basis rejected")
  let target := #v[(1 : Rat), 1]
  require ((babai gap target).distanceSq == 2) "unexpected nearest-plane candidate"
  let cv := closest gap target
  require (cv.distanceSq == 1 && cv.points.map (·.ambient.toList) == [[1, 2]])
    "closest search failed to improve Babai"
  require (checkClosest gap.rows target
    ⟨point gap target #v[0, 1], enumerationCertificate gap target 1⟩)
    "closest certificate rejected"
  require (!checkClosest gap.rows target
    ⟨babai gap target, enumerationCertificate gap target 2⟩)
    "nonoptimal Babai candidate certified as closest"
  match closestWith { nodes := some 0 } gap target with
  | .complete .. => throw (IO.userError "unvisited optimum claimed complete")
  | .incomplete incumbent _ pending phase counts =>
    require (incumbent.distanceSq == 2 && phase == .optimum &&
      !pending.isEmpty && counts.nodes == 0) "interrupted closest progress is incorrect"
  match shortestWith { nodes := some 0 } a2 with
  | some (.incomplete incumbent _ pending phase counts) =>
    require (incumbent.ambient != 0 && phase == .optimum &&
      !pending.isEmpty && counts.nodes == 0) "interrupted shortest progress is incorrect"
  | _ => throw (IO.userError "unvisited shortest search claimed complete")
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
  require (shortestWith {} zero).isNone "budgeted rank-zero shortest is not none"
  require ((babai zero #v[3, 4]).distanceSq == 25) "rank-zero Babai distance"
  let cv0 := closest zero #v[3, 4]
  require (cv0.distanceSq == 25 && cv0.points.map (·.ambient.toList) == [[0, 0]])
    "rank-zero closest failed"

def certificates : IO Unit := do
  let some b := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]])
    | throw (IO.userError "A2 rejected")
  let cert := enumerationCertificate b 0 2
  require (checkEnumeration b.rows 0 2 cert) "native certificate rejected"
  require (!checkEnumerationWith (cert.tree.nodes - 1) b.rows 0 2 cert)
    "replay node budget not enforced"
  require (!checkEnumeration b.rows 0 2 { cert with forward := 0 }) "corrupt transform accepted"
  let badData := { cert.data with norms := #v[(0 : Rat), 1] }
  require (!checkEnumeration b.rows 0 2 { cert with data := badData }) "corrupt norms accepted"
  require (!checkEnumeration b.rows 0 2 { cert with points := cert.points.drop 1 })
    "missing claimed point accepted"
  match cert.tree with
  | .node interval children =>
    require (!checkEnumeration b.rows 0 2
      { cert with tree := .node ⟨interval.lo, interval.hi + 1⟩ children })
      "corrupt endpoint accepted"
    require (!checkEnumeration b.rows 0 2
      { cert with tree := .node interval (children.drop 1) }) "missing branch accepted"
    require (!checkEnumeration b.rows 0 2
      { cert with tree := .node interval (children ++ children.take 1) })
      "duplicate branch accepted"
    match children with
    | (a, .node inner ((c, _) :: tail)) :: rest =>
      let corrupt := Tree.node interval ((a, .node inner ((c, .empty) :: tail)) :: rest)
      require (!checkEnumeration b.rows 0 2 { cert with tree := corrupt }) "missing leaf accepted"
    | _ => throw (IO.userError "unexpected A2 tree")
  | _ => throw (IO.userError "missing A2 tree")
  let some sv := shortest b | throw (IO.userError "missing shortest result")
  let some candidate := sv.points.head? | throw (IO.userError "missing shortest point")
  require (checkShortest b.rows ⟨candidate, cert⟩) "shortest certificate rejected"
  require (!checkShortest b.rows ⟨point b 0 0, cert⟩) "zero certified as shortest"
  require (!checkShortest b.rows ⟨candidate, enumerationCertificate b 0 6⟩)
    "wrong-radius shortest certificate accepted"
  let u := matrix 2 2 [[-1, 0], [0, 1]]
  let some changed := ofMatrix? (u * b.rows) | throw (IO.userError "changed basis rejected")
  let other := enumerationCertificate changed 0 2
  let transported : Certificate 2 3 :=
    { other with
      forward := u
      reverse := u
      points := other.points.map fun p => point b 0 (u.transpose * p.coefficients) }
  require (checkEnumeration b.rows 0 2 transported) "determinant-minus-one transform rejected"
  require (transported.points == cert.points) "original coefficient reconstruction disagrees"

private def rejected (value : Except String α) : Bool :=
  match value with | .error _ => true | .ok _ => false

private def decoding : IO Unit := do
  let some b := ofMatrix? (matrix 2 3 [[1, -1, 0], [0, 1, -1]]) |
    throw (IO.userError "A2 basis rejected")
  let cert := enumerationCertificate b 0 2
  let text := encodeCertificate cert
  let limits : DecodeLimits := {
    bytes := text.utf8ByteSize
    dimension := 3
    nodes := cert.tree.nodes
    points := cert.points.length }
  let .ok decoded := decodeCertificate limits 2 3 text | throw (IO.userError "certificate decode failed")
  require (checkEnumeration b.rows 0 2 decoded) "decoded certificate replay failed"
  require (encodeCertificate decoded == text) "certificate serialization changed"
  require (rejected (decodeCertificate { limits with bytes := text.utf8ByteSize - 1 } 2 3 text))
    "byte limit ignored"
  require (rejected (decodeCertificate { limits with nodes := cert.tree.nodes - 1 } 2 3 text))
    "global tree node limit ignored"
  require (rejected (decodeCertificate { limits with points := cert.points.length - 1 } 2 3 text))
    "point limit ignored"
  require (rejected (decodeCertificate { limits with dimension := 2 } 2 3 text))
    "dimension limit ignored"
  require (rejected (decodeCertificate { limits with digits := 0 } 2 3 text)) "digit limit ignored"
  require (rejected (decodeCertificate {} 3 2 text)) "mismatched dimensions accepted"
  require (rejected (decodeCertificate {} 2 3 (text ++ " trailing"))) "trailing tokens accepted"
  require (rejected (decodeCertificate {} 2 3 "hex-lattice-enum-1 2 3")) "truncation accepted"
  require (rejected (decodeCertificate {} 0 1 "hex-lattice-enum-1 0 1 0 0 E 0"))
    "zero rational denominator accepted"
  require (rejected (decodeCertificate {} 0 0 "hex-lattice-enum-1 0 0 N 0 0 0 0"))
    "tree deeper than rank accepted"
  require (rejected (decodeCertificate {} 0 0 "hex-lattice-enum-1 0 0 E 99999999999999999999"))
    "excessive point count accepted"
  require (rejected (decodeCertificate {} 0 0 "hex-lattice-enum-2 0 0 E 0"))
    "unknown format accepted"
  let .ok empty := decodeCertificate {} 0 0 "hex-lattice-enum-1 0 0 L 1 0 1" |
    throw (IO.userError "rank-zero certificate decode failed")
  require (checkEnumeration (matrix 0 0 []) #v[] 0 empty) "rank-zero decode replay failed"
  let cvp := closestCertificate b #v[1/2, 1/2, 1/2]
  require (checkClosest b.rows #v[1/2, 1/2, 1/2] cvp) "native closest certificate rejected"
  require (checkClosestWith cvp.enumeration.tree.nodes b.rows #v[1/2, 1/2, 1/2] cvp)
    "bounded closest replay rejected exact limit"
  require (!checkClosestWith 0 b.rows #v[1/2, 1/2, 1/2] cvp) "closest replay ignored zero budget"
  require (!checkClosestWith (cvp.enumeration.tree.nodes - 1) b.rows #v[1/2, 1/2, 1/2] cvp)
    "closest replay ignored insufficient budget"
  let cvpText := encodeOptimumCertificate cvp
  let .ok cvpDecoded := decodeOptimumCertificate {} 2 3 cvpText |
    throw (IO.userError "closest certificate decode failed")
  require (checkClosest b.rows #v[1/2, 1/2, 1/2] cvpDecoded) "decoded closest replay failed"
  let some svp := shortestCertificate b | throw (IO.userError "missing native shortest certificate")
  require (checkShortest b.rows svp) "native shortest certificate rejected"
  require (checkShortestWith svp.enumeration.tree.nodes b.rows svp) "bounded shortest replay rejected exact limit"
  require (!checkShortestWith 0 b.rows svp) "shortest replay ignored zero budget"
  require (!checkShortestWith (svp.enumeration.tree.nodes - 1) b.rows svp)
    "shortest replay ignored insufficient budget"
  let .ok svpDecoded := decodeOptimumCertificate {} 2 3 (encodeOptimumCertificate svp) |
    throw (IO.userError "shortest certificate decode failed")
  require (checkShortest b.rows svpDecoded) "decoded shortest replay failed"
  require (rejected (decodeOptimumCertificate { bytes := 0 } 2 3 cvpText))
    "optimum byte limit ignored"
  require (rejected (decodeOptimumCertificate {} 2 3 (cvpText ++ " trailing")))
    "optimum trailing tokens accepted"

private def preprocessing : IO Unit := do
  let some b := ofMatrix? (matrix 2 2 [[1, 100], [0, 1]]) |
    throw (IO.userError "sheared basis rejected")
  let change := lllPreprocess b
  require (Hex.lllReducedCheck change.working.rows (3/4) (11/20)) "preprocessed basis is not LLL-reduced"
  require (Matrix.sameLatticeCert b.rows change.working.rows change.forward change.reverse)
    "LLL transforms failed replay"
  let target : Vector Rat 2 := #v[1/2, -1/2]
  require ((retarget (prepare b 0) target).check) "retargeted preparation failed replay"
  require (change.enumerate target (1/2) == enumerate b target (1/2)) "preprocessed ball changed coefficients"
  require (change.closest target == closest b target) "preprocessed closest vectors changed"
  require (change.shortest == shortest b) "preprocessed shortest vectors changed"
  require (checkEnumeration b.rows target (1/2) (change.certificate target (1/2)))
    "preprocessed ball certificate rejected"
  require (checkClosest b.rows target (change.closestCertificate target)) "preprocessed closest certificate rejected"
  let some sv := change.shortestCertificate | throw (IO.userError "missing preprocessed shortest certificate")
  require (checkShortest b.rows sv) "preprocessed shortest certificate rejected"
  require (checkBasisChange b b.rows (matrix 2 2 [[1, 0], [0, 1]]) (matrix 2 2 [[0, 0], [0, 0]])).isNone
    "invalid reverse transform accepted"
  require (checkBasisChange b (matrix 2 2 [[1, 0], [2, 0]])
    (matrix 2 2 [[1, 0], [0, 1]]) (matrix 2 2 [[1, 0], [0, 1]])).isNone
    "dependent working basis accepted"
  let some empty := ofMatrix? (matrix 0 2 []) | throw (IO.userError "rank-zero basis rejected")
  require ((lllPreprocess empty).closest #v[3, 4] == closest empty #v[3, 4]) "rank-zero preprocessing changed result"
  for budget in ([{ nodes := some 0 }, { answers := some 0 }, { certificateNodes := some 0 }] : List Budget) do
    match change.closestWith budget target with
    | .complete .. => throw (IO.userError "preprocessed budget exhaustion reported complete")
    | .incomplete candidate _ pending _ _ =>
      require (checkPoint b.rows target candidate) "preprocessed partial incumbent reconstruction failed"
      require (!pending.isEmpty) "preprocessed partial result lost pending work"

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
  ball (matrix 1 1 [[1]]) #v[0] 0 [[0]]
  ball (matrix 1 1 [[1]]) #v[-2001/2] (1/4) [[-1001], [-1000]]
  require (ofMatrix? (matrix 2 2 [[1, 2], [2, 4]])).isNone "dependent basis accepted"
  budgets
  minima
  certificates
  decoding
  preprocessing
  IO.println "lattice enumeration conformance passed"

end Hex.LatticeEnum.Conformance

/-- info: lattice enumeration conformance passed -/
#guard_msgs in
#eval Hex.LatticeEnum.Conformance.run
