/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Determinant.Schedules
import Determinant.Fixture
import Determinant.Modular
import Determinant.Univariate

open Hex Determinant.Schedules

namespace Determinant.Runtime

def rational (A : Matrix Int n n) : Matrix Rat n n :=
  Matrix.ofFn fun i j => mkRat A[(i, j)] ((i.val + j.val) % 7 + 1)

/-- Include denominator discovery, matrix scaling, elimination and final
rational normalization in the requested computation. -/
def scaledRat (A : Matrix Rat n n) : Rat :=
  let scales := Vector.ofFn fun i : Fin n =>
    Fin.foldl n (fun d j => Nat.lcm d A[(i, j)].den) 1
  let B : Matrix Int n n := Matrix.ofFn fun i j => A[(i, j)].num * (scales[i] / A[(i, j)].den : Nat)
  mkRat B.bareiss (scales.foldl (· * ·) 1)

def dyadic (A : Matrix Int n n) (spread : Nat) : Matrix Dyadic n n :=
  Matrix.ofFn fun i j => Dyadic.ofIntWithPrec A[(i, j)]
    (((3 * i.val + 5 * j.val) % 8) * spread)

def scaledDyadic (A : Matrix Dyadic n n) : Dyadic :=
  let scales := Vector.ofFn fun i : Fin n =>
    Fin.foldl n (fun p j => max p (A[(i, j)].precision.getD 0)) (0 : Int)
  let B : Matrix Int n n := Matrix.ofFn fun i j => match A[(i, j)] with
    | .zero => 0
    | .ofOdd z p _ => z <<< (scales[i] - p).toNat
  Dyadic.ofIntWithPrec B.bareiss (scales.foldl (· + ·) 0)

def emitInput (A : Matrix R n n) (encode : R → Lean.Json) : IO Unit :=
  IO.println <| (Lean.Json.mkObj [("input", Lean.Json.arr <|
    (Array.finRange n).map fun i => Lean.Json.arr <|
      (Array.finRange n).map fun j => encode A[(i, j)])]).compress

def encodeRat (q : Rat) : Lean.Json := Lean.toJson (q.num, q.den)

def run (kind arm : String) (n bits : Nat) (shape : String) (spread : Nat) : IO Unit := do
  let A := variant (dense n bits) shape
  match kind with
  | "int" =>
    emitInput A Lean.toJson
    if arm ∈ ["stages", "stages-flat", "stages-owned", "stages-word"] then
      return ← Modular.stages arm A
    if arm == "modular" || arm == "divisor" then
      let compute := if arm == "modular" then
          fun M => M.detModular? (ModularMatrix.defaultFuel M)
        else fun M => (M.detViaDivisorWith (Rand.ofSeed 0) (ModularMatrix.defaultFuel M)).1
      return ← timed arm (← IO.mkRef A) compute
        (fun d => d.map toString |>.getD "exhausted")
    let compute := match arm with
      | "bareiss" => Matrix.bareiss
      | "bird" => bird
      | "berkowitz" => berkowitz
      | _ => fun _ => 0
    timed arm (← IO.mkRef A) compute toString
  | "rat" =>
    let B := rational A
    emitInput B encodeRat
    let compute := match arm with
      | "bareiss" => Matrix.bareissWith (fun a b : Rat => if b == 0 then 0 else a / b)
      | "bird" => bird
      | "berkowitz" => berkowitz
      | "scaled" => scaledRat
      | _ => fun _ => 0
    timed arm (← IO.mkRef B) compute (fun q => (encodeRat q).compress)
  | "dyadic" =>
    let B := dyadic A spread
    emitInput B (encodeRat ∘ Dyadic.toRat)
    let compute := match arm with
      | "bird" => bird
      | "berkowitz" => berkowitz
      | "scaled" => scaledDyadic
      | _ => fun _ => 0
    timed arm (← IO.mkRef B) compute (fun d => (encodeRat d.toRat).compress)
  | "poly" =>
    let B : Matrix Poly 4 4 := Matrix.ofFn fun i j =>
      (Determinant.rows.getD i.val []).getD j.val 0
    emitInput B (Lean.toJson ∘ PolyDet.toList)
    let compute := match arm with
      | "bareiss" => PolyDet.polyDet
      | "bird" => bird
      | "berkowitz" => berkowitz
      | _ => fun _ => 0
    timed arm (← IO.mkRef B) compute (fun p => (Lean.toJson (PolyDet.toList p)).compress)
  | "univariate" =>
    emitInput Univariate.dense (Lean.toJson ∘ DensePoly.coeffs)
    if arm == "sparse" then
      timed arm (← IO.mkRef Univariate.sparse) Univariate.sparseCoeffs
        (fun a => (Lean.toJson a).compress)
    else
      let compute := if arm == "interpolate" then Univariate.interpolate
        else fun A => some (Matrix.bareissWith Hex.exactDiv A).coeffs
      timed arm (← IO.mkRef Univariate.dense) compute
        (fun a => a.map (fun a => (Lean.toJson a).compress) |>.getD "nonintegral")
  | _ => throw <| IO.userError "unknown coefficient ring"

end Determinant.Runtime

def main (args : List String) : IO Unit := do
  let [kind, arm, n, bits, shape, spread] := args
    | throw <| IO.userError "expected ring arm dimension bits shape exponent-spread"
  let supported := match kind with
    | "int" => ["bareiss", "bird", "berkowitz", "modular", "divisor", "stages", "stages-flat", "stages-owned", "stages-word"]
    | "rat" => ["bareiss", "bird", "berkowitz", "scaled"]
    | "dyadic" => ["bird", "berkowitz", "scaled"]
    | "poly" => ["bareiss", "bird", "berkowitz"]
    | "univariate" => ["sparse", "dense", "interpolate"]
    | _ => []
  unless arm ∈ supported do throw <| IO.userError "unsupported coefficient operation"
  if kind == "poly" || kind == "univariate" then
    unless n == "4" && bits == "8" && shape == "dense" && spread == "1" do
      throw <| IO.userError "fixed polynomial fixture requires 4 8 dense 1"
  Determinant.Runtime.run kind arm n.toNat! bits.toNat! shape spread.toNat!
