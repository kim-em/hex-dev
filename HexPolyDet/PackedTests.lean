/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDet.Select

open Hex.PolyDet Hex.Matrix Hex.MvPoly.Kernel Hex.Kronecker

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def entrySize (z : Int) : Nat := if z == 0 then 0 else 1
private def bounded (intermediate certificate : Nat) (rows : List (List Int))
    (check := Hex.Matrix.checkDetList 2) :=
  Hex.Matrix.detWitnessBudgeted HexArith.Int.exactDiv 2 entrySize
    ⟨intermediate, certificate⟩ check rows

-- Round admission includes both blocks, and rejects before the final checker.
#guard match bounded 11 100 [[1, 2], [3, 4]] (fun _ _ => false) with
  | .error (.exhausted .intermediate 12 11) => true
  | _ => false
-- The witness budget is checked before its self-check, at the exact boundary.
#guard match bounded 12 3 [[1, 2], [3, 4]] (fun _ _ => false) with
  | .error (.exhausted .certificate 4 3) => true
  | _ => false
#guard match bounded 12 4 [[1, 2], [3, 4]] with
  | .ok w => Hex.Matrix.checkDetList 2 [[1, 2], [3, 4]] w
  | _ => false
-- Pivot swaps and singular witnesses use the same production and validation.
#guard match bounded 7 3 [[0, 2], [3, 4]] with
  | .ok w => Hex.Matrix.checkDetList 2 [[0, 2], [3, 4]] w
  | _ => false
#guard match bounded 100 2 [[1, 2], [1, 2]] with
  | .ok (.singular v) => Hex.Matrix.checkDetList 2 [[1, 2], [1, 2]] (.singular v)
  | _ => false
#guard match bounded 12 4 [[1, 2], [3, 4]] (fun _ _ => false) with
  | .error .rejected => true
  | _ => false
#guard match bounded 100 100 [[1], [2]] with
  | .error (.malformed 2) => true
  | _ => false

private def budget : Budget := { maxDenseDigits := 65536, maxPackedBits := 4096 }
private def one : PolyList Int := [([0], 1)]
private def x : PolyList Int := [([1], 1)]
private def x2 : PolyList Int := [([2], 1)]
private def oneMod : PolyList Nat := [([0], 1)]

example : checkDetPolyPacked .plain 1 0 [] (.triangular [] [] one) = true := by decide +kernel
example : checkDetPolyPacked .plain 1 0 [] (.singular []) = false := by decide +kernel
example : checkDetPolyPacked .plain 1 2 [[x, []], [[], x]]
    (.triangular [] [[one], [[], x]] x2) = true := by decide +kernel
example : checkDetPolyPacked .signedPacked 1 2 [[x, []], [[], x]]
    (.triangular [] [[one], [[], x]] x2) [(32,128),(32,128)] = true := by decide +kernel
example : checkDetPolyPacked .plain 1 2 [[x, x], [x, x]]
    (.singular [one, [([0], -1)]]) = true := by decide +kernel
example : checkDetPolyPacked .plain 1 2 [[x], [x]]
    (.singular [one, [([0], -1)]]) = false := by decide +kernel

-- The permuted integer prefixes are [1] and [2,1], with residue targets [1] and [0,1].
example : checkDetPolyPackedMod .plain 2 1 2
    [[oneMod, oneMod], [oneMod, []]]
    (.triangular [(0, 1)] [[oneMod], [oneMod, oneMod]] oneMod)
    [[[]], [one, []]] = true := by decide +kernel
example : checkDetPolyPackedMod .plain 2 1 2
    [[oneMod, oneMod], [oneMod, []]]
    (.triangular [(0, 1)] [[oneMod], [oneMod, oneMod]] oneMod)
    [[[]], [[], []]] = false := by decide +kernel

example : checkDetPolyPackedMod .plain 2 1 2
    [[oneMod, oneMod], [oneMod, oneMod]] (.singular [oneMod, oneMod])
    [[one, one]] = true := by decide +kernel
example : checkDetPolyPackedMod .plain 2 1 0 [] (.triangular [] [] oneMod)
    [] = true := by decide +kernel

example : checkMulTermsMod budget .plain 1 1 2 1 2 [[one, one]] [[one], [one]]
    [[[]]] [[one]] = true := by decide +kernel
example : checkMulTermsMod budget .plain 1 1 2 1 2 [[one, one]] [[one], [one]]
    [[x]] [[one]] = false := by decide +kernel

-- Exact degree/bit boundaries for x*x = x²: 3 dense digits, 8 packed bits.
example : checkMulTerms { maxDenseDigits := 3, maxPackedBits := 8 } .plain
    1 1 1 1 [[x]] [[x]] [[x2]] = true := by decide +kernel
example : checkMulTerms { maxDenseDigits := 2, maxPackedBits := 8 } .plain
    1 1 1 1 [[x]] [[x]] [[x2]] = false := by decide +kernel
example : checkMulTerms { maxDenseDigits := 3, maxPackedBits := 7 } .plain
    1 1 1 1 [[x]] [[x]] [[x2]] = false := by decide +kernel

example : checkDetPolyPackedMod .signedPacked 2 1 2
    [[oneMod, oneMod], [oneMod, []]]
    (.triangular [(0, 1)] [[oneMod], [oneMod, oneMod]] oneMod)
    [[[]], [one, []]] [(32,128),(32,128)] = true := by decide +kernel
example : checkDetPolyPackedMod .plain 2 1 2
    [[oneMod, oneMod], [oneMod, []]]
    (.triangular [(0, 1)] [[oneMod], [oneMod, oneMod]] oneMod)
    [[[]], [one]] = false := by decide +kernel
example : checkDetPolyPackedMod .plain 2 1 2
    [[oneMod, oneMod], [oneMod, []]]
    (.triangular [(0, 1)] [[oneMod], [oneMod, oneMod]] oneMod)
    [[[]], [[([1], 0), ([0], 1)], []]] = false := by decide +kernel
example : checkDetPolyPacked .plain 1 1 [[one]]
    (.triangular [(0,0)] [[one]] one) = false := by decide +kernel
example : checkDetPolyPacked .plain 1 1 [[one]]
    (.triangular [] [[x]] one) = false := by decide +kernel
example : checkDetPolyPacked .plain 1 1 [[one]]
    (.triangular [] [[one, one]] one) = false := by decide +kernel
example : checkDetPolyPacked .plain 1 1 [[one]]
    (.triangular [] [[one]] [([],1)]) = false := by decide +kernel

open Hex.PolyDet.Packed in
#guard (prepareQuotients {} 2
  [{ row := 0, inner := 2, width := 1, left := [one,one], right := [[one],[one]], result := [[]] }]).toOption ==
  some [[one]]
open Hex.PolyDet.Packed in
#guard (match prepareQuotients {} 2
  [{ row := 0, inner := 2, width := 1, left := [one,one], right := [[one],[one]], result := [x] }] with
  | .error e => e == .indivisible 0 0 | .ok _ => false)
open Hex.PolyDet.Packed in
#guard (match prepareQuotients { certificateTerms := 0 } 2
  [{ row := 0, inner := 2, width := 1, left := [one,one], right := [[one],[one]], result := [[]] }] with
  | .error e => e == .unavailable | .ok _ => false)

open Hex.PolyDet.Packed in
#guard (select budget .automatic 1 (products (Hex.PolyDet.ops 1) 1 [[x]]
  (.triangular [] [[one]] x)) (table := [])).toOption.map (·.reason) == some (some "no measured packed regime")
open Hex.PolyDet.Packed in
#guard (select budget .packed 1 (products (Hex.PolyDet.ops 1) 1 [[x]]
  (.triangular [] [[one]] x))).toOption.map (·.packed) == some true
open Hex.PolyDet.Packed in
#guard (select budget .packed 1 (products (Hex.PolyDet.ops 1) 1 [[x]]
  (.triangular [] [[one]] x)) (some 2)).toOption.map (·.reason) ==
  some (some "residue quotient payload unavailable")

-- Every product must be covered before automatic selection packs the witness.
open Hex.PolyDet.Packed in
#guard Id.run do
  let ps := products (Hex.PolyDet.ops 1) 2 [[x, []], [[], x]]
    (.triangular [] [[one], [[], x]] x2)
  let .ok forced := select budget .packed 1 ps | return false
  let keys := forced.reports.map (·.key)
  let .ok covered := select budget .automatic 1 ps (table := keys) | return false
  let .ok uncovered := select budget .automatic 1 ps (table := keys.take 1) | return false
  return covered.packed && covered.mode == .plain && !uncovered.packed

-- A measured witness must select packing with the shipped table, without an override.
private def measuredRows : List (List (PolyList Int)) :=
  [[[([2, 0], -3), ([1, 0], -6), ([0, 1], -9), ([0, 0], -3)],
    [([2, 0], -2), ([1, 0], -4), ([0, 1], -6), ([0, 0], -2)],
    [([2, 0], -3), ([1, 0], -6), ([0, 1], -9), ([0, 0], -3)],
    [([2, 0], 3), ([1, 0], 6), ([0, 1], 9), ([0, 0], 3)]],
   [[([1, 0], -1), ([0, 2], -2), ([0, 1], -3), ([0, 0], -2)],
    [([1, 0], 1), ([0, 2], 2), ([0, 1], 3), ([0, 0], 2)],
    [([1, 0], -3), ([0, 2], -6), ([0, 1], -9), ([0, 0], -6)],
    [([1, 0], -1), ([0, 2], -2), ([0, 1], -3), ([0, 0], -2)]],
   [[([2, 0], 9), ([1, 0], 3), ([0, 2], 9), ([0, 1], 6)],
    [([2, 0], 9), ([1, 0], 3), ([0, 2], 9), ([0, 1], 6)],
    [([2, 0], -6), ([1, 0], -2), ([0, 2], -6), ([0, 1], -4)],
    [([2, 0], -3), ([1, 0], -1), ([0, 2], -3), ([0, 1], -2)]],
   [[([2, 0], 3), ([1, 0], 9), ([0, 2], 3), ([0, 1], 6)],
    [([2, 0], 2), ([1, 0], 6), ([0, 2], 2), ([0, 1], 4)],
    [([2, 0], -1), ([1, 0], -3), ([0, 2], -1), ([0, 1], -2)],
    [([2, 0], -1), ([1, 0], -3), ([0, 2], -1), ([0, 1], -2)]]]

open Hex.PolyDet.Packed in
#guard Id.run do
  let a := measuredRows
  let decode := Hex.MvPoly.Kernel.denote (n := 2) (cmp := Hex.Mono.grevlex)
  let .ok w := detWitnessWith Hex.exactDiv 4 (Hex.PolyDet.check 4)
    (a.map (List.map decode)) | return false
  let w := w.map Hex.PolyDet.toList
  let .ok s := select {} .automatic 2 (products (Hex.PolyDet.ops 2) 4 a w) | return false
  return s.packed && s.mode == .plain

open Hex.PolyDet.Packed in
#guard (match prepareQuotients {} 0 [] with
  | .error e => e == .invalidModulus | .ok _ => false)
open Hex.PolyDet.Packed in
#guard (select budget .lists 1 (products (Hex.PolyDet.ops 1) 1 [[x]]
  (.triangular [] [[one]] x)) (some 2)).toOption.map (·.reason) ==
  some (some "forced term lists")

-- Caller-supplied packing widths are hints whose side conditions are checked.
example : checkDetPolyPacked .signedPacked 1 2 [[x, []], [[], x]]
    (.triangular [] [[one], [[], x]] x2) [(1,1),(1,1)] = false := by decide +kernel

-- Admission does not waive the retained-support check after an elimination round.
#guard match Hex.Matrix.detWitnessBudgeted (fun (_ _ : Int) => (100 : Int)) 2 Int.natAbs
    ⟨14, 1000⟩ (fun _ _ => false) [[1,1],[1,2]] with
  | .error (.exhausted .intermediate 403 14) => true
  | _ => false
