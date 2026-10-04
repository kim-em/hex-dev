/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootPolicy
public import HexSignDet.Codec
public import HexOrderedFn.Infinitesimal

public section

open Hex Hex.RealClosure Hex.RealClosure.Isolation
open Hex.SignDet.Codec (Json)

private def object (fields : List (String × Json)) : Json :=
  .object (fields.foldr (fun entry rest => .cons entry.1 entry.2 rest) .nil)

private def printJson (value : Json) : IO Unit := do
  let some text := String.fromUTF8? value.writeBytes
    | throw (IO.userError "JSON printer emitted invalid UTF-8")
  IO.println text.trimAsciiEnd.toString

private def rational (a : Rat) : Json := .arr #[Json.of a.num, Json.of a.den]

private def fraction (a : RationalFn Rat) : Json := object [
  ("num", .arr (a.num.toArray.map rational)), ("den", .arr (a.den.toArray.map rational))]

private def emit {E : Type} [Zero E] [DecidableEq E] [One E] [Add E]
    [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [Div E]
    (policy : Policy) (name : String) (sign : E → Int) (encode : E → Json) (p : DensePoly E)
    : IO Unit := do
  let context : Nat := 10378
  let output := match Roots.Policy.roots? policy sign context p with
    | .error error => object [("error", .string (reprStr error))]
    | .ok .all => object [("kind", .string "all")]
    | .ok (.finite entries) => object [("kind", .string "finite"),
        ("entries", .arr (entries.toArray.map fun entry =>
          let root := match entry.root with
            | .point value => object [("kind", .string "point"), ("value", encode value)]
            | .selected d => object [("kind", .string "selected"),
                ("context", Json.of d.raw.context),
                ("head", .arr (d.raw.head.toArray.map encode)),
                ("lower", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.lower),
                ("upper", SignDet.Codec.endpoint
                  ⟨encode, fun _ => .error "encode only"⟩ d.raw.upper),
                ("indices", Json.of d.raw.indices), ("signs", Json.of d.raw.signs)]
          object [("root", root), ("multiplicity", Json.of entry.multiplicity)]))]
  let fields := [("case", .string name), ("mode", .string "assembly"),
    ("head", .arr (p.toArray.map encode)), ("output", output)]
  printJson (object [("policy", .string (reprStr policy)), ("result", object fields)])

def main : IO Unit := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - 2
  let repeated := DensePoly.scale (-3) (x * x * quadratic * quadratic * quadratic *
    (x - 3) * (x - 3) * (x - 3) * (x - 3) * (x - 3))
  let cut : DensePoly Rat := DensePoly.ofCoeffs #[3, -5, 2]
  let cases := [("zero", (0 : DensePoly Rat)), ("constant", DensePoly.C 5),
    ("pure power", DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, -5]),
    ("repeated factors", repeated), ("root-free factor", (x*x+1)*(x*x+1)*(x-1)),
    ("simple zero", x*(x-1)*(x-1)), ("cut point", cut*cut)]
  let epsilon : RationalFn Rat := RationalFn.X
  let y : DensePoly (RationalFn Rat) := DensePoly.ofCoeffs #[0, 1]
  let first := y - DensePoly.C epsilon
  let second := y - DensePoly.C (2*epsilon)
  for policy in [Policy.standard, .bounded, .whole] do
    for (name, p) in cases do
      emit policy name Sturm.orderSign rational p
    emit policy "infinitesimal repeated pair" (OrderedFn.Infinitesimal.sign Sturm.orderSign)
      fraction (DensePoly.scale 2 (first*first*second*second*second))
    emit policy "inverse infinitesimal" (OrderedFn.Infinitesimal.sign Sturm.orderSign)
      fraction (y - DensePoly.C epsilon⁻¹)
    emit policy "infinitesimal squarefree pair" (OrderedFn.Infinitesimal.sign Sturm.orderSign)
      fraction (first*second)
    emit policy "infinitesimal same-label pair" (OrderedFn.Infinitesimal.sign Sturm.orderSign)
      fraction (DensePoly.scale 3 (first*second*first*second))

