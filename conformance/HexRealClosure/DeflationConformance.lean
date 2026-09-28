/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Deflation
public import HexRealClosure.Bisection
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

private def endpoint {E : Type} (encode : E → Lean.Json) : Endpoint E → Lean.Json
  | .finite a => Lean.Json.mkObj [("finite", encode a)]
  | .negInf => .str "-infinity"
  | .posInf => .str "+infinity"

private def emitSplit {E : Type} [Zero E] [DecidableEq E] [One E]
    [Add E] [Sub E] [Mul E] [Neg E] [NatCast E] [Inv E]
    (name : String) (depth : Nat) (encode : E → Lean.Json) (sign : E → Int)
    (p : DensePoly E) (lower upper : E) : IO Unit := do
  let point := Bisection.midpoint lower upper
  let result := Bisection.bisect? sign p lower upper
  let payload := result.map fun split => Lean.Json.mkObj [
    ("removed", (split.mode.removed.map encode).getD .null),
    ("active", .arr (split.mode.head.toArray.map encode)),
    ("left_head", .arr (split.left.head.toArray.map encode)),
    ("right_head", .arr (split.right.head.toArray.map encode)),
    ("left_lower", endpoint encode split.left.lower),
    ("left_upper", endpoint encode split.left.upper),
    ("right_lower", endpoint encode split.right.lower),
    ("right_upper", endpoint encode split.right.upper),
    ("left_count", Lean.toJson (Sturm.queryPrepared split.left 1)),
    ("right_count", Lean.toJson (Sturm.queryPrepared split.right 1))]
  IO.println (Lean.Json.mkObj [
    ("kind", .str "bisection"), ("name", .str name), ("depth", Lean.toJson depth),
    ("coefficients", .arr (p.toArray.map encode)), ("lower", encode lower),
    ("upper", encode upper), ("point", encode point),
    ("original_count", Lean.toJson (Sturm.query sign p 1 (.finite lower) (.finite upper))),
    ("result", payload.getD .null)]).compress

private def emitRatSplit := emitSplit (E := Rat) (depth := 0)
  (encode := fun a => .str (toString a)) (sign := Sturm.orderSign)

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

  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - DensePoly.C 2
  let cubic := quadratic * linearFactor (1 : Rat)
  emitRatSplit "split cubic root cut" (DensePoly.scale 3 cubic) 0 2
  emitRatSplit "split negative cubic" (DensePoly.scale (-3) cubic) 0 2
  emitRatSplit "split fractional cubic" (DensePoly.scale (1 / 2) cubic) 0 2
  emitRatSplit "split regular quadratic" quadratic 0 2
  emitRatSplit "split zero" 0 0 2
  emitRatSplit "split repeated root" (linearFactor (1 : Rat) * linearFactor 1) 0 2
  emitRatSplit "split reversed interval" quadratic 2 0
  emitRatSplit "split root endpoint" (linearFactor (1 : Rat) * linearFactor 3) 1 4
  emitRatSplit "split roots on both sides of root cut" cubic (-2) 4
  emitRatSplit "split roots on both sides of regular cut" quadratic (-2) 2
  emitRatSplit "split linear root to constant" (linearFactor (1 : Rat)) 0 2
  emitRatSplit "split constant" (DensePoly.C 3) 0 2
  let sign₁ := OrderedFn.Infinitesimal.sign OrderedFn.orderSign
  emitSplit "split close infinitesimal roots" 1 fraction sign₁ close 0 1
  emitSplit "split infinitesimal root cut" 1 fraction sign₁
    (linearFactor epsilon * linearFactor (3 * epsilon)) 0 (2 * epsilon)
  emitSplit "split inverse infinitesimal root" 1 fraction sign₁
    (linearFactor epsilon⁻¹ * linearFactor (3 * epsilon⁻¹)) 0 (2 * epsilon⁻¹)
  emitSplit "split infinitesimal root endpoint" 1 fraction sign₁ close epsilon 1
  emitSplit "split infinitesimal roots on both sides" 1 fraction sign₁
    (linearFactor epsilon * linearFactor (-epsilon)) (-1) 1
  let sign₂ := OrderedFn.Infinitesimal.sign sign₁
  emitSplit "split first infinitesimal root" 2 nestedFraction sign₂ nested 0 (2 * first)
  emitSplit "split second infinitesimal root" 2 nestedFraction sign₂
    (linearFactor delta * linearFactor (3 * delta)) 0 (2 * delta)
  emitSplit "split nested roots before fallback" 2 nestedFraction sign₂ nested 0 1
  emitSplit "split nested root endpoint" 2 nestedFraction sign₂ nested delta 1
