/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRootPolicy
public meta import HexRealClosure.TowerRootPolicy

public section

open Hex Hex.RealClosure

private def run : IO Unit := do
  let registry : BaseContext.Registry := fun _ => none
  let base := Tower.Context.base (BaseContext.rational registry)
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let two : base.Value := 1 + 1
  let three := two + 1
  let q := x*x - DensePoly.C two
  let p := DensePoly.scale (-three) (x*x*q*q*q)
  for policy in [Isolation.Policy.standard, .bounded, .whole] do
    let .ok .all := base.rootsWith? policy 0
      | throw (IO.userError "native policy zero lost all-roots case")
    let .ok (.finite entries) := base.rootsWith? policy p
      | throw (IO.userError "native policy repeated roots failed")
    unless entries.map (·.multiplicity) == [3, 2, 3] do
      throw (IO.userError "native policy detached multiplicities")
    for entry in entries do
      unless entry.root.signAt p == 0 &&
          entry.root.context.signature.base == base.signature.base &&
          entry.root.context.signature.roots.length ≤ 1 do
        throw (IO.userError "native policy root equation or ownership failed")
    for (a,b) in entries.zip entries.tail do
      unless a.root.compare b.root == .lt do
        throw (IO.userError "native policy roots lost strict ordering")
  IO.println "native policy roots retain equations, owners, order and multiplicities"

#eval run
