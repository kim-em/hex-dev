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

private def check {registry : BaseContext.Registry} (base : Tower.Context registry)
    (p : DensePoly base.Value) (labels : List Nat) : IO Unit := do
  let .ok (.finite standard) := base.rootsWith? .standard p
    | throw (IO.userError "native standard policy failed")
  for policy in [Isolation.Policy.standard, .bounded, .whole] do
    let .ok .all := base.rootsWith? policy 0
      | throw (IO.userError "native policy zero lost all-roots case")
    let .all := base.rootsWith policy 0
      | throw (IO.userError "ordinary native policy zero lost all-roots case")
    let .ok (.finite entries) := base.rootsWith? policy p
      | throw (IO.userError "native policy repeated roots failed")
    let .finite ordinary := base.rootsWith policy p
      | throw (IO.userError "ordinary native policy roots failed")
    unless entries.map (·.multiplicity) == labels &&
        entries.length == standard.length && ordinary.length == entries.length do
      throw (IO.userError "native policy detached multiplicities")
    for entry in entries do
      let ownerDepth := match entry.root with
        | .point _ => base.signature.roots.length
        | .selected _ _ _ => base.signature.roots.length + 1
      unless entry.root.signAt p == 0 &&
          entry.root.context.signature.base == base.signature.base &&
          entry.root.context.signature.roots.length == ownerDepth do
        throw (IO.userError "native policy root equation or ownership failed")
    for (a,b) in entries.zip entries.tail do
      unless a.root.compare b.root == .lt do
        throw (IO.userError "native policy roots lost strict ordering")
    for others in [standard, ordinary] do
      for (a,b) in entries.zip others do
        unless a.root.compare b.root == .eq && a.multiplicity == b.multiplicity do
          throw (IO.userError "native policies changed ordered values or multiplicities")

private def run : IO Unit := do
  let registry : BaseContext.Registry := fun _ => none
  let base := Tower.Context.base (BaseContext.rational registry)
  let x : DensePoly base.Value := DensePoly.ofCoeffs #[0, 1]
  let two : base.Value := 1 + 1
  let three := two + 1
  let q := x*x - DensePoly.C two
  let p := DensePoly.scale (-three) (x*x*q*q*q)
  check base p [3, 2, 3]
  let .ok (.finite [_negative, positive]) := base.rootsWith? .standard q
    | throw (IO.userError "could not construct algebraic predecessor")
  let parent := positive.root.context
  unless parent.signature.roots.length == 1 && parent.sign positive.root.value == 1 do
    throw (IO.userError "algebraic predecessor was not the positive square root")
  let y : DensePoly parent.Value := DensePoly.ofCoeffs #[0, 1]
  check parent (y*y - DensePoly.C positive.root.value) [1, 1]
  IO.println "native policy roots retain ordered values, labels and exact owners over rational and algebraic parents"

#eval run
