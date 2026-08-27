/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexPolyFast
import HexModArith.Ntt.Butterfly
import HexModArith.Ntt.Catalogue
import HexModArith.Ntt.Convolution
import HexModArith.Ntt.CrtInput
import HexPolyFp.NttMul
import HexPolyZ.KroneckerMulti
import HexPolyZ.NttMul

/-!
JSONL fixtures for the generic hex-poly-fast surface.

The stream records the public integer dispatcher's selected kernel and
exercises multiplication, clipped products, division, exact Euclidean APIs,
cyclic products, multipoint evaluation, interpolation, and both Padé result
forms. The companion FLINT/exact-Python driver independently recomputes polynomial
arithmetic and checks Bézout and Padé relations rather than duplicating Hex's
implementation choices.
-/

namespace HexPolyFast.Emit

open Hex Hex.DensePoly
open Hex.Conformance.Emit

private def lib : String := "HexPolyFast"

private def intPoly (coeffs : List Int) : DensePoly Int :=
  ofList coeffs

private def ratPoly (coeffs : List Int) : DensePoly Rat :=
  ofList (coeffs.map Rat.ofInt)

private def ratCoeffs (p : DensePoly Rat) : List Rat :=
  p.toArray.toList

private def namedIntPolyValue (kernel : String) (p : DensePoly Int) : String :=
  "{\"kernel\":\"" ++ kernel ++ "\",\"coeffs\":" ++
    polyValue p.toArray.toList ++ "}"

private def ratPairValue (a b : DensePoly Rat) : String :=
  "[" ++ polyRatValue (ratCoeffs a) ++ "," ++
    polyRatValue (ratCoeffs b) ++ "]"

private def xgcdValue (g s t : DensePoly Rat) : String :=
  "{\"gcd\":" ++ polyRatValue (ratCoeffs g) ++
    ",\"left\":" ++ polyRatValue (ratCoeffs s) ++
    ",\"right\":" ++ polyRatValue (ratCoeffs t) ++ "}"

private def xgcdLeftValue (g s : DensePoly Rat) : String :=
  "{\"gcd\":" ++ polyRatValue (ratCoeffs g) ++
    ",\"left\":" ++ polyRatValue (ratCoeffs s) ++ "}"

private def padeValue (p q : DensePoly Rat) : String :=
  "{\"p\":" ++ polyRatValue (ratCoeffs p) ++
    ",\"q\":" ++ polyRatValue (ratCoeffs q) ++ "}"

private def natPairValue (left right : Nat) : String :=
  "[" ++ toString left ++ "," ++ toString right ++ "]"

private def selectionValue {n bound : Nat}
    (selection : ZMod64.Ntt.CrtSelection n bound) : String :=
  "{\"count\":" ++ toString selection.primes.length ++
    ",\"product\":" ++
      toString (selection.primes.map ZMod64.NttPrime.modulus).prod ++ "}"

private structure MulCase where
  id : String
  left : List Int
  right : List Int
  cutoff : Nat := 32

private def oddCoeffs (n salt : Nat) : List Int :=
  (List.range n).map fun i =>
    Int.ofNat (((i + 5) * (salt + 7)) % 29 + 1) - 14

private def mulCases : List MulCase := [
  { id := "mul/both-empty", left := [], right := [] },
  { id := "mul/one-empty", left := [3, -2, 5], right := [] },
  { id := "mul/constants", left := [-7], right := [9] },
  { id := "mul/trailing-zero", left := [3, -2, 5, 0, 0], right := [1, 4, 0] },
  { id := "mul/cutoff-31", left := oddCoeffs 31 3, right := oddCoeffs 33 11 },
  { id := "mul/cutoff-32", left := oddCoeffs 32 5, right := oddCoeffs 32 13 },
  { id := "mul/cutoff-33", left := oddCoeffs 33 7, right := oddCoeffs 31 17 },
  { id := "mul/ratio-under-2", left := oddCoeffs 128 31, right := oddCoeffs 80 37 },
  { id := "mul/ratio-2", left := oddCoeffs 16 17, right := oddCoeffs 8 19 },
  { id := "mul/ratio-4", left := oddCoeffs 16 19, right := oddCoeffs 4 23 },
  { id := "mul/ratio-16", left := oddCoeffs 16 23, right := oddCoeffs 1 29 },
  { id := "mul/ratio-64", left := oddCoeffs 64 29, right := [-3] }
]

private def emitMulCase (c : MulCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let left := intPoly c.left
  let right := intPoly c.right
  let plan : MulPlan Int := karatsubaPlan c.cutoff
  emitResult lib c.id "mul"
    (polyValue (mulWith plan left right).toArray.toList)
  emitResult lib c.id "square"
    (polyValue (squareWith plan left).toArray.toList)

private structure SliceCase where
  id : String
  left : List Int
  right : List Int
  lo : Nat
  len : Nat

private def sliceCases : List SliceCase := [
  { id := "slice/empty", left := [], right := [1, 2], lo := 0, len := 0 },
  { id := "slice/one", left := [2, -1, 3], right := [4, 5], lo := 0, len := 1 },
  { id := "slice/last", left := [2, -1, 3], right := [4, 5], lo := 3, len := 1 },
  { id := "slice/normalized-output", left := [1, 1], right := [1, -1],
    lo := 0, len := 2 },
  { id := "slice/out-of-range", left := [2, -1, 3], right := [4, 5], lo := 20, len := 4 },
  { id := "slice/middle", left := oddCoeffs 33 23, right := oddCoeffs 17 29,
    lo := 16, len := 33 }
]

private def emitSliceCase (c : SliceCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let left := intPoly c.left
  let right := intPoly c.right
  let value := mulSlice (karatsubaPlan 32) c.lo c.len left right
  emitResult lib c.id s!"slice/{c.lo}/{c.len}"
    (polyValue value.toArray.toList)

private def emitMiddle : IO Unit := do
  let leftCoeffs := oddCoeffs 33 41
  let rightCoeffs := oddCoeffs 17 43
  let left := intPoly leftCoeffs
  let right := intPoly rightCoeffs
  let lo := right.size - 1
  let len := left.size - right.size + 1
  emitPolyFixture lib "middle/checked/left" leftCoeffs
  emitPolyFixture lib "middle/checked/right" rightCoeffs
  emitResult lib "middle/checked" s!"slice/{lo}/{len}"
    (polyValue (mulMiddleChecked (karatsubaPlan 32) left right).toArray.toList)

private structure RatPairCase where
  id : String
  left : List Int
  right : List Int

private def divisionCases : List RatPairCase := [
  { id := "divmod/zero-divisor", left := [3, -2, 5], right := [] },
  { id := "divmod/constant", left := [3, -2, 5], right := [2] },
  { id := "divmod/larger-divisor", left := [1, 2], right := [3, 0, 1] },
  { id := "divmod/exact", left := [-2, 5, -5, 3, 3], right := [-1, 2, 1] },
  { id := "divmod/general", left := [2, -3, 0, 5, 1, -7, 4], right := [2, -3, 5] }
]

private def gcdCases : List RatPairCase := [
  { id := "gcd/zero-zero", left := [], right := [] },
  { id := "gcd/left-zero", left := [], right := [2, -3, 1] },
  { id := "gcd/right-zero", left := [2, -3, 1], right := [] },
  { id := "gcd/associates", left := [2, -4, 2], right := [-3, 6, -3] },
  { id := "gcd/reversed", left := [-1, 0, 1], right := [-2, 1, 0, 1] },
  { id := "gcd/shared", left := [-2, 1, 1, 0, 1], right := [2, -3, 0, 1] }
]

private def emitRatInputs (c : RatPairCase) : IO (DensePoly Rat × DensePoly Rat) := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  return (ratPoly c.left, ratPoly c.right)

private def emitDivisionCase (c : RatPairCase) : IO Unit := do
  let (left, right) ← emitRatInputs c
  let (q, r) := divModWith (karatsubaPlan 2) left right
  emitResult lib c.id "divmod" (ratPairValue q r)

private def emitGcdCase (c : RatPairCase) : IO Unit := do
  let (left, right) ← emitRatInputs c
  let plan : MulPlan Rat := karatsubaPlan 2
  let x := xgcdWith plan left right
  let xl := xgcdLeftWith plan left right
  emitResult lib c.id "gcd" (polyRatValue (ratCoeffs (gcdWith plan left right)))
  emitResult lib c.id "xgcd" (xgcdValue x.gcd x.left x.right)
  emitResult lib c.id "xgcd_left" (xgcdLeftValue xl.gcd xl.left)

private structure CyclicCase where
  id : String
  left : List Int
  right : List Int
  n : Nat

private def cyclicCases : List CyclicCase := [
  { id := "cyclic/unit", left := [1], right := [2, 3], n := 1 },
  { id := "cyclic/odd", left := [1, 2, 3], right := [4, 5], n := 3 },
  { id := "cyclic/wrap", left := [3, -2, 1, 4], right := [-1, 5, 2], n := 4 }
]

private def emitCyclicCase (c : CyclicCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let left := intPoly c.left
  let right := intPoly c.right
  emitResult lib c.id s!"cyclic/{c.n}"
    (match mulCyclic? (karatsubaPlan 2) c.n left right with
      | none => "null"
      | some p => polyValue p.toArray.toList)
  emitResult lib c.id s!"negacyclic/{c.n}"
    (match mulNegacyclic? (karatsubaPlan 2) c.n left right with
      | none => "null"
      | some p => polyValue p.toArray.toList)

private def emitEval : IO Unit := do
  let points : Array Int := #[-3, 0, 2, 5, 9]
  let polynomial : DensePoly Int := intPoly [7, -4, 3, 2, -1]
  emitPolyFixture lib "eval/points" points.toList
  emitPolyFixture lib "eval/polynomial" polynomial.toArray.toList
  let plan := EvalPlan.build (karatsubaPlan 2) points
  emitResult lib "eval" "eval_many"
    (intListValue (plan.eval polynomial).toList)
  let largePolynomial : DensePoly Int := intPoly [1, 2, 3, 4, 5, 6, 7]
  emitPolyFixture lib "eval-large/points" points.toList
  emitPolyFixture lib "eval-large/polynomial" largePolynomial.toArray.toList
  emitResult lib "eval-large" "eval_many"
    (intListValue (plan.eval largePolynomial).toList)
  emitPolyFixture lib "eval-empty/points" []
  emitPolyFixture lib "eval-empty/polynomial" polynomial.toArray.toList
  emitResult lib "eval-empty" "eval_many"
    (intListValue ((EvalPlan.build (karatsubaPlan 2) (#[] : Array Int)).eval polynomial).toList)

private def emitInterpolation : IO Unit := do
  let points : Array Rat := #[-1, 0, 2, 4]
  let values : Array Rat := #[6, 3, 3, 11]
  emitPolyFixture lib "interpolate/points" (points.toList.map (·.num))
  emitPolyFixture lib "interpolate/values" (values.toList.map (·.num))
  match InterpPlan.build? (karatsubaPlan 2) points with
  | none => emitResult lib "interpolate" "interpolate" "null"
  | some plan =>
      match plan.interpolate? values with
      | none => emitResult lib "interpolate" "interpolate" "null"
      | some p =>
          emitResult lib "interpolate" "interpolate" (polyRatValue (ratCoeffs p))
  emitPolyFixture lib "interpolate-duplicate/points" [1, 2, 1]
  emitPolyFixture lib "interpolate-duplicate/values" [3, 4, 5]
  let duplicate := (InterpPlan.build? (karatsubaPlan 2) (#[1, 2, 1] : Array Rat)).bind
    (fun plan => plan.interpolate? (#[3, 4, 5] : Array Rat))
  emitResult lib "interpolate-duplicate" "interpolate"
    (match duplicate with | none => "null" | some p => polyRatValue (ratCoeffs p))
  emitPolyFixture lib "interpolate-mismatch/points" [0, 1, 2]
  emitPolyFixture lib "interpolate-mismatch/values" [4, 5]
  let mismatch := (InterpPlan.build? (karatsubaPlan 2) (#[0, 1, 2] : Array Rat)).bind
    (fun plan => plan.interpolate? (#[4, 5] : Array Rat))
  emitResult lib "interpolate-mismatch" "interpolate"
    (match mismatch with | none => "null" | some p => polyRatValue (ratCoeffs p))
  let widePoints : Array Rat := #[-4, -3, -2, -1, 0, 1, 2, 3]
  let widePolynomial : DensePoly Rat := ofList [1, 2, 3, 4, 5, 6, 7, 8]
  let wideValues := widePoints.map (widePolynomial.eval ·)
  emitPolyFixture lib "interpolate-wide/points" (widePoints.toList.map (·.num))
  emitPolyFixture lib "interpolate-wide/values" (wideValues.toList.map (·.num))
  let wide := (InterpPlan.build? (karatsubaPlan 2) widePoints).bind
    (fun plan => plan.interpolate? wideValues)
  emitResult lib "interpolate-wide" "interpolate"
    (match wide with | none => "null" | some p => polyRatValue (ratCoeffs p))

private def emitPadeCase {k : Nat} (id : String) (series : TSeries Rat k)
    (m n : Nat) : IO Unit := do
  emitSeriesFixture lib (id ++ "/series") "QQ" k series.coeffs.toArray.toList
  let homogeneous := padeHomogeneous (karatsubaPlan 2) series m n
  emitResult lib id s!"pade_homogeneous/{m}/{n}"
    (padeValue homogeneous.p homogeneous.q)
  emitResult lib id s!"pade/{m}/{n}"
    (match pade? (karatsubaPlan 2) series m n with
      | none => "null"
      | some approx => padeValue approx.p approx.q)

private def emitPade : IO Unit := do
  let unit : TSeries Rat 3 := TSeries.ofFn fun _ => 1
  let nonunit : TSeries Rat 3 := TSeries.ofFn fun i => if i = 2 then 1 else 0
  let zero : TSeries Rat 5 := 0
  let empty : TSeries Rat 0 := TSeries.ofFn fun _ => 0
  let wide : TSeries Rat 9 :=
    TSeries.ofFn fun i => [1, 2, -1, 3, 0, 4, -2, 1, 5].getD i 0
  emitPadeCase "pade/unit" unit 1 1
  emitPadeCase "pade/nonunit" nonunit 1 1
  emitPadeCase "pade/zero" zero 2 2
  emitPadeCase "pade/numerator-constant" unit 0 1
  emitPadeCase "pade/denominator-constant" unit 1 0
  emitPadeCase "pade/precision-zero" empty 2 2
  emitPadeCase "pade/wide" wide 4 4

/-! Coefficient-owner kernels share this monorepo driver so the JSONL surface
also records forced KS and direct/CRT-NTT results without moving those kernels
out of their owning libraries. -/

private instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

private theorem primeFive : Hex.Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hmle : m ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) hm
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hm
    · exact Or.inl rfl
    · simp at hm
    · simp at hm
    · simp at hm
    · exact Or.inr rfl

private instance primeModulusFive : ZMod64.PrimeModulus 5 :=
  ZMod64.primeModulusOfPrime primeFive

private def fpFive (coeffs : List Nat) : FpPoly 5 :=
  ofList (coeffs.map fun n => ZMod64.ofNat 5 n)

private def fpCoeffs (p : FpPoly 5) : List Int :=
  p.toArray.toList.map fun x => Int.ofNat x.toNat

private def emitFpInputs (id : String) (left right : List Nat) : IO Unit := do
  emitPolyFixture lib (id ++ "/left") (left.map Int.ofNat) (some 5)
  emitPolyFixture lib (id ++ "/right") (right.map Int.ofNat) (some 5)

private def emitForwardButterfly (id : String) (xValue yValue : Nat)
    (hx : xValue < 2 * 5) (hy : yValue < 2 * 5) : IO Unit := do
  emitPolyFixture lib (id ++ "/input") [Int.ofNat xValue, Int.ofNat yValue] (some 5)
  let twiddle := ZMod64.NttTwiddle.ofValue (ZMod64.ofNat 5 2)
  let x : ZMod64.NttRaw2 5 := ZMod64.Ntt.raw2OfNat xValue hx
  let y : ZMod64.NttRaw2 5 := ZMod64.Ntt.raw2OfNat yValue hy
  let output := ZMod64.Ntt.forwardButterfly twiddle x y
  emitResult lib id "ntt_forward_butterfly/5/2"
    (natPairValue output.1.val.toNat output.2.val.toNat)

private def emitInverseButterfly (id : String) (xValue yValue : Nat)
    (hx : xValue < 4 * 5) (hy : yValue < 4 * 5) : IO Unit := do
  emitPolyFixture lib (id ++ "/input") [Int.ofNat xValue, Int.ofNat yValue] (some 5)
  let twiddle := ZMod64.NttTwiddle.ofValue (ZMod64.ofNat 5 2)
  let x : ZMod64.NttRaw4 5 := ZMod64.Ntt.raw4OfNat xValue hx
  let y : ZMod64.NttRaw4 5 := ZMod64.Ntt.raw4OfNat yValue hy
  let output := ZMod64.Ntt.inverseButterfly twiddle x y
  emitResult lib id "ntt_inverse_butterfly/5/2"
    (natPairValue output.1.val.toNat output.2.val.toNat)

private def emitButterflyBoundaries : IO Unit := do
  emitForwardButterfly "ntt/butterfly-forward/zero" 0 0 (by decide) (by decide)
  emitForwardButterfly "ntt/butterfly-forward/p-minus-one" 0 4 (by decide) (by decide)
  emitForwardButterfly "ntt/butterfly-forward/p" 0 5 (by decide) (by decide)
  emitForwardButterfly "ntt/butterfly-forward/two-p-minus-one" 0 9 (by decide) (by decide)
  emitForwardButterfly "ntt/butterfly-forward/first-two-p-minus-one" 9 0
    (by decide) (by decide)
  emitForwardButterfly "ntt/butterfly-forward/both-two-p-minus-one" 9 9
    (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/zero" 0 0 (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/p-minus-one" 0 4 (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/p" 0 5 (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/two-p-minus-one" 0 9 (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/four-p-minus-one" 0 19
    (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/first-two-p-minus-one" 9 0
    (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/both-two-p-minus-one" 9 9
    (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/first-four-p-minus-one" 19 0
    (by decide) (by decide)
  emitInverseButterfly "ntt/butterfly-inverse/both-four-p-minus-one" 19 19
    (by decide) (by decide)

private def emitCrtSelectionBoundaries : IO Unit := do
  let first := ZMod64.nttPrimes[0]'(by decide)
  let below := (first.modulus - 1) / 2
  let above := (first.modulus + 1) / 2
  for (id, bound) in [("below", below), ("above", above)] do
    let selection := ZMod64.Ntt.CrtSelection.build? 1 bound
    emitResult lib ("ntt/crt-bound/" ++ id) s!"crt_selection/1/{bound}"
      (match selection with
        | none => "null"
        | some selected => selectionValue selected)

private def emitNtt : IO Unit := do
  emitButterflyBoundaries
  emitCrtSelectionBoundaries
  let root2 := ZMod64.ofNat 5 4
  let plan2 := ZMod64.NttPlan.build? (p := 5) (n := 2) root2
  emitResult lib "ntt/plan-2" "ntt_plan/5/2/4" (boolValue plan2.isSome)
  emitPolyFixture lib "ntt/roundtrip/input" [3, 4] (some 5)
  match plan2 with
  | none =>
      emitResult lib "ntt/roundtrip" "ntt_forward/5" "null"
      emitResult lib "ntt/roundtrip" "ntt_roundtrip/5" "null"
  | some plan =>
      match ZMod64.Ntt.forward? plan #[ZMod64.ofNat 5 3, ZMod64.ofNat 5 4] with
      | none =>
          emitResult lib "ntt/roundtrip" "ntt_forward/5" "null"
          emitResult lib "ntt/roundtrip" "ntt_roundtrip/5" "null"
      | some transformed =>
          emitResult lib "ntt/roundtrip" "ntt_forward/5"
            (intListValue (transformed.toList.map fun x => Int.ofNat x.toNat))
          emitResult lib "ntt/roundtrip" "ntt_roundtrip/5"
            (match ZMod64.Ntt.inverse? plan transformed with
              | none => "null"
              | some values =>
                  intListValue (values.toList.map fun x => Int.ofNat x.toNat))

  let directLeft := [1, 1]
  let directRight := [1, 2]
  emitFpInputs "ntt/direct-fp" directLeft directRight
  let direct := (ZMod64.NttPlan.build? (p := 5) (n := 4) (ZMod64.ofNat 5 2)).bind
    (fun plan => FpPoly.mulNtt? plan (fpFive directLeft) (fpFive directRight))
  emitResult lib "ntt/direct-fp" "fp_direct_ntt/5"
    (match direct with | none => "null" | some p => polyValue (fpCoeffs p))

  let crtLeft := [4, 0, 3]
  let crtRight := [2, 1, 4]
  emitFpInputs "ntt/crt-fp" crtLeft crtRight
  emitResult lib "ntt/crt-fp" "fp_crt_ntt/5"
    (match FpPoly.mulNttCrt? (fpFive crtLeft) (fpFive crtRight) with
      | none => "null"
      | some p => polyValue (fpCoeffs p))

  emitPolyFixture lib "ntt/crt-z/left" [1, -2, 3]
  emitPolyFixture lib "ntt/crt-z/right" [4, 5]
  emitResult lib "ntt/crt-z" "z_crt_ntt"
    (match ZPoly.mulNttCrt? (intPoly [1, -2, 3]) (intPoly [4, 5]) with
      | none => "null"
      | some p => polyValue p.toArray.toList)

  let prime := ZMod64.nttPrimes[6]'(by decide)
  let maxLength := ZMod64.NttPrime.maxLength prime
  -- The owner conformance module proves support at `maxLength` without
  -- allocating its enormous twiddle table.  These executable cases call the
  -- catalogue API at both small lengths and on the cheap capacity miss.
  for n in [1, 2, maxLength + 1] do
    let supported := (prime.plan? n).isSome
    emitResult lib s!"ntt/capacity/{n}" s!"ntt_capacity/{prime.maxLog}/{n}"
      (boolValue supported)

private structure KsCase where
  id : String
  left : List Int
  right : List Int

private def ksCases : List KsCase := [
  { id := "ks/signed-small", left := [-17, 0, 31, -32], right := [7, -9, 2] },
  { id := "ks/power-boundary", left := [255, -256, 257], right := [-127, 128, 129] },
  { id := "ks/asymmetric", left := oddCoeffs 3 31,
    right := (oddCoeffs 64 37).map fun x => x * Int.ofNat (2 ^ 73) }
]

private def emitKsCase (c : KsCase) : IO Unit := do
  emitPolyFixture lib (c.id ++ "/left") c.left
  emitPolyFixture lib (c.id ++ "/right") c.right
  let left := intPoly c.left
  let right := intPoly c.right
  emitResult lib c.id "ks1" (polyValue (ZPoly.mulKroneckerAt 0 0 left right).toArray.toList)
  emitResult lib c.id "ks2" (polyValue (ZPoly.mulKS2 left right).toArray.toList)
  emitResult lib c.id "ks3" (polyValue (ZPoly.mulKS3 left right).toArray.toList)
  emitResult lib c.id "ks4" (polyValue (ZPoly.mulKS4 left right).toArray.toList)

private def emitDispatch : IO Unit := do
  let left : ZPoly := ofList (List.replicate 24 (Int.ofNat (2 ^ 63)))
  let right : ZPoly := ofList (List.replicate 24 (-(Int.ofNat (2 ^ 63))))
  emitPolyFixture lib "dispatch/left" left.toArray.toList
  emitPolyFixture lib "dispatch/right" right.toArray.toList
  emitResult lib "dispatch" "z_dispatch"
    (namedIntPolyValue (ZPoly.selectKernel left right).name (ZPoly.mulFast left right))

private def emitAll : IO Unit := do
  for c in mulCases do emitMulCase c
  for c in sliceCases do emitSliceCase c
  emitMiddle
  for c in divisionCases do emitDivisionCase c
  for c in gcdCases do emitGcdCase c
  for c in cyclicCases do emitCyclicCase c
  emitEval
  emitInterpolation
  emitPade
  emitNtt
  for c in ksCases do emitKsCase c
  emitDispatch

end HexPolyFast.Emit

def main : IO Unit :=
  HexPolyFast.Emit.emitAll
