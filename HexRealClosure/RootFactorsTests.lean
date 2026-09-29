/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootFactors

public section

open Hex Hex.RealClosure

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def checkZero : IO Unit :=
  match Roots.assemble Sturm.orderSign (10378 : Nat) (0 : DensePoly Rat) with
  | .ok .all => pure ()
  | _ => throw (IO.userError "zero polynomial lost its all-roots case")

private def checkConstant (constant : Rat) : IO Unit :=
  match Roots.assemble Sturm.orderSign (10378 : Nat) (DensePoly.C constant) with
  | .ok (.finite []) => pure ()
  | _ => throw (IO.userError "nonzero constant has roots or failed")

private def run : IO Unit := do
  checkZero
  checkConstant 5
  checkConstant (-3)
  let power : DensePoly Rat := DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, -5]
  match Roots.assemble Sturm.orderSign (10378 : Nat) power with
  | .ok (.finite [entry]) =>
    require (entry.multiplicity == 6) "wrong pure-power zero multiplicity"
    match entry.root with
    | .point value => require (value == 0) "wrong pure-power root"
    | _ => throw (IO.userError "pure-power zero is not a coefficient point")
  | _ => throw (IO.userError "pure power did not yield exactly zero")
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let quadratic := x * x - 2
  let linear := x - 3
  let p := DensePoly.scale (-3) (x * x * quadratic * quadratic * quadratic *
    linear * linear * linear * linear * linear)
  let .ok (.finite entries) := Roots.assemble Sturm.orderSign (10378 : Nat) p
    | throw (IO.userError "repeated-factor root assembly failed")
  require (entries.map (·.multiplicity) == [2, 3, 3, 5]) "wrong original multiplicities"
  match entries with
  | [zero, negative, positive, three] =>
    match zero.root with
    | .point value => require (value == 0) "restored zero is not zero"
    | _ => throw (IO.userError "zero was not restored as a coefficient point")
    match negative.root.compare (.point (-1)), positive.root.compare (.point 1),
        three.root.compare (.point 3) with
    | .ok .lt, .ok .gt, .ok .eq => pure ()
    | _, _, _ => throw (IO.userError "labels belong to incorrect root values")
  | _ => throw (IO.userError "wrong root count after Yun and zero extraction")
  IO.println "zero, constants and original root multiplicity assembly checks passed"

#eval run
