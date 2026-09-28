/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Deflation
public import HexOrderedFn.Infinitesimal
public import Lean.Data.Json.Printer
public import Lean.Data.Json.FromToJson.Basic

public section

open Hex Hex.RealClosure

private def fraction (f : RationalFn Rat) : Lean.Json :=
  Lean.Json.mkObj [
    ("num", .arr (f.num.toArray.map fun a => .str (toString a))),
    ("den", .arr (f.den.toArray.map fun a => .str (toString a)))]

private def nestedFraction (f : RationalFn (RationalFn Rat)) : Lean.Json :=
  Lean.Json.mkObj [
    ("num", .arr (f.num.toArray.map fraction)),
    ("den", .arr (f.den.toArray.map fraction))]

private def emit {E : Type} [Zero E] [DecidableEq E] [One E]
    [Add E] [Sub E] [Mul E] (name : String) (depth : Nat)
    (encode : E → Lean.Json) (p : DensePoly E) (root : E) : IO Unit := do
  let result := deflate? p root
  IO.println (Lean.Json.mkObj [
    ("name", .str name), ("depth", Lean.toJson depth),
    ("coefficients", .arr (p.toArray.map encode)), ("root", encode root),
    ("quotient", (result.map fun d => .arr (d.quotient.toArray.map encode)).getD .null),
    ("remaining_at_root", (result.map fun d => encode (d.quotient.eval root)).getD .null)]).compress

private def emitRat := emit (E := Rat) (depth := 0) (encode := fun a => .str (toString a))

def main : IO Unit := do
  emitRat "zero" 0 0
  emitRat "constant" (DensePoly.C 3) 0
  emitRat "not a root" (DensePoly.ofCoeffs #[-2, 0, 1]) 1
  emitRat "linear" (DensePoly.ofCoeffs #[0, 1]) 0
  emitRat "nonmonic fractional root" (DensePoly.ofCoeffs #[-2, 3]) (2 / 3)
  emitRat "negative leading coefficient" (DensePoly.ofCoeffs #[2, -3]) (2 / 3)
  emitRat "reducible nonmonic" ((DensePoly.ofCoeffs #[-2, 0, 1]) * linearFactor (3 : Rat) * DensePoly.C 5) 3
  emitRat "repeated root" (DensePoly.ofCoeffs #[1, -2, 1]) 1
  let epsilon : RationalFn Rat := RationalFn.X
  let close := linearFactor epsilon * linearFactor (2 * epsilon)
  emit "close roots" 1 fraction close epsilon
  emit "nonroot between close roots" 1 fraction close (epsilon / 2)
  emit "inverse infinitesimal" 1 fraction (linearFactor epsilon⁻¹ * linearFactor 3) epsilon⁻¹
  let delta : RationalFn (RationalFn Rat) := RationalFn.X
  let first : RationalFn (RationalFn Rat) := RationalFn.C epsilon
  let nested := linearFactor first * linearFactor delta
  emit "remove second infinitesimal" 2 nestedFraction nested delta
  emit "remove first infinitesimal" 2 nestedFraction nested first
