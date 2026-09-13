/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Polynomial
public import HexPoly

public section

namespace Hex.Matrix.PolyWitness

private abbrev QPoly := DensePoly Rat

private instance : Inhabited QPoly := ⟨0⟩

private def mulMod (f a b : QPoly) : QPoly := (a * b) % f

private def inverse (f a : QPoly) : QPoly :=
  if a.isZero then 0 else
    let t := DensePoly.xgcdLeftMonic a f
    if t.gcd.size = 1 then (DensePoly.scale (1 / t.gcd.leadingCoeff) t.left) % f else 0

private structure Elimination where
  matrix : Array (Array QPoly)
  rows : Array Nat
  cols : Array Nat

/-- Untrusted Gaussian elimination. Each pivot inverse is computed once and
shared across its row, rather than recomputed for every fraction-free quotient. -/
private def eliminate (f : QPoly) (input : Array (Array QPoly)) (width : Nat) : Elimination := Id.run do
  let mut A := input
  let mut rows := Array.range A.size
  let mut cols := #[]
  let mut r := 0
  for j in [:width] do
    if r = A.size then break
    let mut pivot : Option Nat := none
    for i in [r:A.size] do
      if pivot.isNone && !(A[i]!)[j]!.isZero then pivot := some i
    if let some i := pivot then
      let row := A[r]!
      A := (A.set! r A[i]!).set! i row
      let name := rows[r]!
      rows := (rows.set! r rows[i]!).set! i name
      let inv := inverse f (A[r]!)[j]!
      let normalized := A[r]!.map (fun a => mulMod f a inv)
      A := A.set! r normalized
      for i in [:A.size] do
        if i != r then
          let c := (A[i]!)[j]!
          if !c.isZero then
            A := A.set! i (A[i]!.mapIdx fun k a => a - mulMod f c normalized[k]!)
      cols := cols.push j
      r := r + 1
  return ⟨A, rows.extract 0 r, cols⟩

private def inverseMatrix (f : QPoly) (B : Array (Array QPoly)) : Array (Array QPoly) :=
  let n := B.size
  let augmented := B.mapIdx fun i row => row ++ (Array.range n).map (fun j => if i = j then 1 else 0)
  (eliminate f augmented n).matrix.map (·.extract n (2 * n))

private def asRat (a : List Int) : QPoly := DensePoly.ofList (a.map Rat.ofInt)

private def asInt (a : QPoly) : Except String (List Int) :=
  a.coeffs.toList.mapM fun q =>
    if q.den = 1 then pure q.num else throw "a polynomial division witness is not integral"

private def quotient (f a : QPoly) : Except String QPoly :=
  let qr := DensePoly.divMod a f
  if qr.2.isZero then pure qr.1 else throw "a polynomial relation has nonzero remainder"

private def dotPoly (a b : List QPoly) : QPoly :=
  (a.zip b).foldl (fun s (a, b) => s + a * b) 0

private structure Data where
  rank : Nat
  rows : List Nat
  cols : List Nat
  vt : List (List QPoly)
  lowerQuot : List (List QPoly)
  denom : Int
  z : List (List (List Int))
  upperQuot : List (List (List Int))

/-- Run elimination over rational polynomial coordinates and clear the
resulting exact row coefficients. The modular witnesses are reductions of
rational identities, so no finite-field inversion algorithm is needed. -/
private def prepare (n m : Nat) (f : List Int) (L : List (List (List Int))) :
    Except String Data := do
  let fp := asRat f
  if fp.natDegree = 0 then throw "the defining polynomial must have positive degree"
  let rawA := (Array.range n).map fun i => (Array.range m).map fun j =>
    asRat (nth [] (nth [] L i) j)
  let A := rawA.map (·.map (· % fp))
  let reduced := eliminate fp A m
  let rows := reduced.rows.toList
  let cols := reduced.cols.toList
  let r := rows.length
  let B := reduced.rows.map fun i => reduced.cols.map fun j => (A[i]!)[j]!
  let rawB := reduced.rows.map fun i => reduced.cols.map fun j => (rawA[i]!)[j]!
  let vt := (List.range r).map fun j =>
    let k := j + 1
    let inv := inverseMatrix fp ((B.extract 0 k).map (·.extract 0 k))
    (List.range k).map fun i => (inv[i]!)[j]!
  let lowerQuot ← (List.range r).mapM fun i =>
    (List.range (r - i)).mapM fun offset => do
      let j := i + offset
      quotient fp (dotPoly rawB[i]!.toList (vt[j]?.getD []) - if j = i then 1 else 0)
  let nonPivot := (List.range n).filter fun i => !RankWitness.memNat i rows
  let invB := inverseMatrix fp B
  let weights := nonPivot.map fun i => (List.range r).map fun l =>
    (List.range r).foldl
      (fun s k => s + mulMod fp (A[i]!)[reduced.cols[k]!]! (invB[k]!)[l]!) 0
  let denom : Nat := weights.foldl (fun d row => row.foldl
    (fun d p => p.coeffs.foldl (fun d q => Nat.lcm d q.den) d) d) 1
  let z ← weights.mapM (·.mapM fun p => asInt (DensePoly.scale (denom : Rat) p))
  let upperQuot ← (nonPivot.zip z).mapM fun (i, zrow) =>
    (List.range m).mapM fun j => do
      let p := rows.map fun l => (rawA[l]!)[j]!
      let q ← quotient fp (DensePoly.scale (denom : Rat) (rawA[i]!)[j]! - dotPoly (zrow.map asRat) p)
      asInt q
  return ⟨r, rows, cols, vt, lowerQuot, denom, z, upperQuot⟩

private def reduceRat (M : Nat) (q : Rat) : Except String Int := do
  let some inv := invMod? q.den M | throw s!"a coordinate denominator is not a unit modulo {M}"
  return ((RankWitness.residue M q.num * inv) % M : Nat)

private def reducePoly (M : Nat) (p : QPoly) : Except String (List Int) :=
  p.coeffs.toList.mapM (reduceRat M)

private def finish (n m : Nat) (f : List Int) (L : List (List (List Int)))
    (d : Data) (M : Nat) : Except String Hex.Matrix.PolyWitness := do
  let some inv := invMod? (RankWitness.residue M (f.getLastD 0)) M |
    throw s!"the leading coefficient is not a unit modulo {M}"
  let vt ← d.vt.mapM (·.mapM (reducePoly M))
  let lowerQuot ← d.lowerQuot.mapM (·.mapM (reducePoly M))
  let w : Hex.Matrix.PolyWitness :=
    ⟨d.rank, M, inv, d.rows, d.cols, vt, lowerQuot, d.denom, d.z, d.upperQuot⟩
  if checkRankPoly n m f L w then return w
  throw s!"the polynomial witness fails its own check modulo {M}"

/-- Produce a list certificate over an integer polynomial quotient. The
defining polynomial should be primitive and irreducible; a violated producer
precondition results in a failed self-check, never an unchecked certificate. -/
def produce (n m : Nat) (f : List Int) (L : List (List (List Int)))
    (moduli : List Nat := witnessModuli) :
    Except String Hex.Matrix.PolyWitness := do
  let d ← prepare n m f L
  let rec tryModuli : List Nat → List String → Except String Hex.Matrix.PolyWitness
    | [], errors => throw (String.intercalate "; " errors.reverse)
    | M :: rest, errors => match finish n m f L d M with
      | .ok w => pure w
      | .error e => tryModuli rest (e :: errors)
  tryModuli moduli []

end Hex.Matrix.PolyWitness
