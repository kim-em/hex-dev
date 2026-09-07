/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRationalFn.Workloads

namespace Hex.RationalFnFixtures
open DensePoly RationalFn RationalFnFamilies
open RationalFnScaling (output)

private def polyJson (p : DensePoly Rat) : Lean.Json :=
  Lean.toJson (p.toArray.map fun c => (c.num, c.den))

private def rawJson (p q : DensePoly Rat) : Lean.Json :=
  Lean.Json.mkObj [("num", polyJson p), ("den", polyJson q)]

private def fractionJson (f : RationalFn Rat) := rawJson f.num f.den

private def sizeJson (p : DensePoly Rat) : Lean.Json :=
  Lean.Json.mkObj [("length", Lean.toJson p.size),
    ("numerator_bits", Lean.toJson (p.toArray.foldl
      (fun b c => max b c.num.natAbs.log2) 0 + 1)),
    ("denominator_bits", Lean.toJson (p.toArray.foldl
      (fun b c => max b c.den.log2) 0 + 1))]

private def emit (name op : String) (n : Nat) (operands : Array Lean.Json)
    (expected : RationalFn Rat) (stages : List (String × DensePoly Rat) := [])
    (exponent : Nat := 0) : IO Unit :=
  IO.println (Lean.Json.mkObj [
    ("schema_version", Lean.toJson (1 : Nat)), ("domain", Lean.toJson "QQ"),
    ("parameter", Lean.toJson n), ("benchmark", Lean.toJson name),
    ("operation", Lean.toJson op), ("operands", Lean.Json.arr operands),
    ("exponent", Lean.toJson exponent), ("expected", fractionJson expected),
    ("intermediate_hex_sizes", Lean.Json.mkObj (stages.map fun (k, p) => (k, sizeJson p)))]).compress

private def normalization (name : String) (n : Nat) (i : Raw) : IO Unit := do
  let f := fraction i.p i.q
  let d := commonWith defaultPlan i.p i.q
  let a := (divModWith defaultPlan i.p d).1
  let b := (divModWith defaultPlan i.q d).1
  emit name "normalize" n #[rawJson i.p i.q] f
    [("monic_gcd", d), ("numerator_cofactor", a), ("denominator_cofactor", b)]

private def binary (name op : String) (n : Nat) (i : Pair) : IO Unit := do
  let f := i.f
  let g := i.g
  let expected := match op with
    | "add" => f + g | "sub" => f - g | "mul" => f * g | _ => f / g
  let numerator := if op == "div" then defaultPlan.mul f.num g.den
    else if op == "mul" then defaultPlan.mul f.num g.num
    else if op == "sub" then defaultPlan.mul f.num g.den - defaultPlan.mul g.num f.den
    else defaultPlan.mul f.num g.den + defaultPlan.mul g.num f.den
  let denominator := defaultPlan.mul f.den (if op == "div" then g.num else g.den)
  emit name op n #[fractionJson f, fractionJson g] expected
    [("uncancelled_numerator", numerator), ("uncancelled_denominator", denominator)]

private def derivative (name : String) (n : Nat) (f : RationalFn Rat) : IO Unit := do
  let numerator := defaultPlan.mul f.num.derivative f.den -
    defaultPlan.mul f.num f.den.derivative
  let denominator := defaultPlan.square f.den
  emit name "derivative" n #[fractionJson f] (RationalFn.derivative f)
    [("quotient_rule_numerator", numerator), ("quotient_rule_denominator", denominator),
     ("cancelled_gcd", commonWith defaultPlan numerator denominator)]

/-- QQ comparator inputs are exactly the native prepared operands. Parameter
zero supplies a small-input control, not an asymptotic observation. -/
def emitFixtures : IO Unit := do
  for n in [0, 32, 64, 128, 256, 512, 1024, 2048, 4096] do
    for name in ["normalizeDegree", "checkedFraction"] do
      normalization s!"Hex.RationalFnFamilies.{name}" n (degreeInput n)
    normalization "Hex.RationalFnFamilies.normalizeCancel" n (cancelInput n)
    let c := coprimePair n
    let k := cancelPair n
    for (name, op, i) in [
        ("addCoprime", "add", c), ("addShared", "add", sharedPair n),
        ("addCancel", "add", sharedCancelPair n), ("addTotal", "add", zeroSumPair n),
        ("addEqual", "add", { k with g := k.f }), ("subtract", "sub", c),
        ("multiply", "mul", c), ("cancelMultiply", "mul", k),
        ("divide", "div", c), ("checkedDivide", "div", c)] do
      binary s!"Hex.RationalFnFamilies.{name}" op n i
    let f := inverseInput n
    for name in ["inverse", "checkedInverse"] do
      emit s!"Hex.RationalFnFamilies.{name}" "inv" n #[fractionJson f] f⁻¹
    for (name, f) in [
        ("derivative", RationalFnWorkloads.linearFraction n),
        ("derivativeCancel", RationalFnWorkloads.squareDenominator n),
        ("derivativePolynomial", RationalFnWorkloads.polynomial n)] do
      derivative s!"Hex.RationalFnWorkloads.{name}" n f
    binary "Hex.RationalFnWorkloads.multiply" "mul" n (RationalFnWorkloads.balanced n)
    let f := RationalFnWorkloads.polynomial n
    emit "Hex.RationalFnWorkloads.square" "pow" n #[fractionJson f] (f ^ (2 : Nat))
      (exponent := 2)
  for n in [0, 128, 256, 512, 1024, 2048, 4096, 8192, 16384] do
    normalization "Hex.RationalFnWorkloads.heightNormalize" n (RationalFnWorkloads.heightRaw n)
    let i := RationalFnWorkloads.heightPair n
    binary "Hex.RationalFnWorkloads.heightAdd" "add" n i
    binary "Hex.RationalFnWorkloads.heightMultiply" "mul" n { i with g := i.f }
    derivative "Hex.RationalFnWorkloads.heightDerivative" n i.f

end Hex.RationalFnFixtures
