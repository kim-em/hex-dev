/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bounds
public import HexOrderedFn.Infinitesimal
public import Lean.Data.Json.Printer
public import Lean.Data.Json.FromToJson.Basic

public section

open Hex Hex.RealClosure

private def emit (name : String) (p : DensePoly Rat) : IO Unit := do
  let value := (Bounds.find? Sturm.orderSign p).map (fun b => b.value)
  IO.println (Lean.Json.mkObj [
    ("kind", .str "rational"), ("name", .str name),
    ("coefficients", .arr (p.toArray.map fun a => .str (toString a))),
    ("bound", value.map (fun a => .str (toString a)) |>.getD .null)]).compress

private def fraction (f : RationalFn Rat) : Lean.Json :=
  Lean.Json.mkObj [
    ("num", .arr (f.num.toArray.map fun a => .str (toString a))),
    ("den", .arr (f.den.toArray.map fun a => .str (toString a)))]

private def nestedFraction (f : RationalFn (RationalFn Rat)) : Lean.Json :=
  Lean.Json.mkObj [
    ("num", .arr (f.num.toArray.map fraction)),
    ("den", .arr (f.den.toArray.map fraction))]

private def emitFirst (name : String) (p : DensePoly (RationalFn Rat)) : IO Unit := do
  let value := (Bounds.find? (OrderedFn.Infinitesimal.sign Sturm.orderSign) p).map
    (fun b => b.value)
  let expected : RationalFn Rat := 2
  if name == "close roots" then
    unless value == some expected do throw (IO.userError "close-root bound failed")
  else
    unless value.isNone do throw (IO.userError "inverse-infinitesimal bound accepted")
  IO.println (Lean.Json.mkObj [
    ("kind", .str "infinitesimal"), ("name", .str name),
    ("depth", Lean.toJson (1 : Nat)), ("coefficients", .arr (p.toArray.map fraction)),
    ("bound", if value.isNone then .null else .str "2")]).compress

def main : IO Unit := do
  emit "zero" 0
  emit "constant" (DensePoly.C (3 / 2))
  emit "sqrt two" (DensePoly.ofCoeffs #[-2, 0, 1])
  emit "negative leading coefficient" (DensePoly.ofCoeffs #[2, 0, -1])
  emit "nonmonic" (DensePoly.ofCoeffs #[-3, 0, 2])
  emit "fractional coefficients" (DensePoly.ofCoeffs #[3 / 7, -2 / 3, 5 / 4])
  emit "strict threshold" (DensePoly.ofCoeffs #[-3, 1])
  emit "last candidate" (DensePoly.ofCoeffs #[-14, 1])
  emit "failure at last candidate" (DensePoly.ofCoeffs #[-15, 1])
  emit "root beyond all candidates" (DensePoly.ofCoeffs #[-1000, 2])
  let epsilon : RationalFn Rat := RationalFn.X
  emitFirst "inverse infinitesimal" (DensePoly.ofCoeffs #[-epsilon⁻¹, 1])
  let x : DensePoly (RationalFn Rat) := DensePoly.ofCoeffs #[0, 1]
  emitFirst "close roots" ((x - DensePoly.C epsilon) * (x - DensePoly.C (2 * epsilon)))
  let delta : RationalFn (RationalFn Rat) := RationalFn.X
  let sign := OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign Sturm.orderSign)
  let p : DensePoly (RationalFn (RationalFn Rat)) := DensePoly.ofCoeffs #[-delta⁻¹, 1]
  unless (Bounds.find? sign p).isNone do throw (IO.userError "nested infinitesimal bound accepted")
  IO.println (Lean.Json.mkObj [
    ("kind", .str "infinitesimal"), ("name", .str "inverse second infinitesimal"),
    ("depth", Lean.toJson (2 : Nat)), ("coefficients", .arr (p.toArray.map nestedFraction)),
    ("bound", .null)]).compress
