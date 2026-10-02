/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.CompleteRoots

public section

open Hex Hex.RealClosure

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def checkZero : IO Unit :=
  match Roots.roots Sturm.orderSign (10378 : Nat) (0 : DensePoly Rat) with
  | .all => pure ()
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
  let .finite entries := Roots.roots Sturm.orderSign (10378 : Nat) p
    | throw (IO.userError "repeated-factor complete roots failed")
  require (entries.length == 4) "wrong root count after Yun and zero extraction"
  require (entries.map (·.multiplicity) == [3, 2, 3, 5]) "sorted multiplicities were detached"
  for (left, right) in entries.zip entries.tail do
    require ((left.root.compare right.root).toOption == some .lt)
      "complete roots are not strictly increasing across factors"
  let mut counts := #[0, 0, 0, 0]
  for entry in entries do
    match entry.root.compare (.point 0), entry.root.compare (.point 3) with
    | .ok .eq, _ =>
      require (entry.multiplicity == 2) "wrong restored zero label"
      match entry.root with
      | .point value => require (value == 0) "restored zero is not zero"
      | _ => throw (IO.userError "zero was not restored as a coefficient point")
      counts := counts.modify 0 (· + 1)
    | _, .ok .eq =>
      require (entry.multiplicity == 5) "wrong root-three label"
      counts := counts.modify 3 (· + 1)
    | .ok .lt, _ =>
      require (entry.multiplicity == 3) "wrong negative root label"
      require ((entry.root.compare (.point (-1))).toOption == some .lt) "incorrect negative root"
      counts := counts.modify 1 (· + 1)
    | .ok .gt, _ =>
      require (entry.multiplicity == 3) "wrong positive root label"
      require ((entry.root.compare (.point 1)).toOption == some .gt) "incorrect positive root"
      counts := counts.modify 2 (· + 1)
    | _, _ => throw (IO.userError "root classification failed")
  require (counts == #[1, 1, 1, 1]) "incorrect root multiset"
  let noRoots : DensePoly Rat := x * x + 1
  match Roots.assemble Sturm.orderSign (10378 : Nat) noRoots with
  | .ok (.finite []) => pure ()
  | _ => throw (IO.userError "positive-degree root-free polynomial failed")
  let mixed : DensePoly Rat := noRoots * noRoots * (x - 1)
  match Roots.assemble Sturm.orderSign (10378 : Nat) mixed with
  | .ok (.finite [entry]) =>
    require (entry.multiplicity == 1) "root-free factor changed real-root multiplicity"
    require ((entry.root.compare (.point 1)).toOption == some .eq) "root-free factor changed real root"
  | _ => throw (IO.userError "mixed real and root-free factors failed")
  let cutFactor : DensePoly Rat := DensePoly.ofCoeffs #[3, -5, 2]
  match Roots.assemble Sturm.orderSign (10378 : Nat) (cutFactor * cutFactor) with
  | .ok (.finite entries) =>
    require (entries.length == 2) "nonzero cut point changed root count"
    require (entries.any fun entry => entry.multiplicity == 2 &&
      match entry.root with
      | .point value => value == 1
      | _ => false) "nonzero cut point or its multiplicity was lost"
    require (entries.any fun entry => entry.multiplicity == 2 &&
      (entry.root.compare (.point (3 / 2))).toOption == some .eq)
      "second nonzero root or its multiplicity was lost"
  | _ => throw (IO.userError "nonzero cut-point assembly failed")
  let simpleZero : DensePoly Rat := x * (x - 1) * (x - 1)
  match Roots.assemble Sturm.orderSign (10378 : Nat) simpleZero with
  | .ok (.finite entries) =>
    require (entries.length == 2) "simple zero was duplicated or lost"
    require (entries.any fun entry => entry.multiplicity == 1 &&
      (entry.root.compare (.point 0)).toOption == some .eq) "simple zero label was lost"
    require (entries.any fun entry => entry.multiplicity == 2 &&
      (entry.root.compare (.point 1)).toOption == some .eq) "double nonzero label was lost"
  | _ => throw (IO.userError "simple zero and repeated nonzero assembly failed")
  let .some selected := Root.validate 7
      { context := 7, head := DensePoly.ofCoeffs #[-2, 0, 1],
        lower := .finite 1, upper := .finite 2, indices := [], signs := [] }
    | throw (IO.userError "selected coefficient root validation failed")
  let handle := selected.handle
  let alpha : Root.Handle.Value handle := Root.Handle.Value.ofPoly handle x
  let y : DensePoly (Root.Handle.Value handle) := DensePoly.ofCoeffs #[0, 1]
  match Roots.assemble Root.Handle.Value.sign (10378 : Nat) (y - DensePoly.C alpha) with
  | .ok (.finite [entry]) =>
    require (entry.multiplicity == 1) "wrong selected-coefficient root multiplicity"
    require ((entry.root.compare (.point alpha)).toOption == some .eq) "wrong selected-coefficient root"
  | _ => throw (IO.userError "selected-coefficient root assembly failed")
  IO.println "zero, constants and original root multiplicity assembly checks passed"

#eval run
