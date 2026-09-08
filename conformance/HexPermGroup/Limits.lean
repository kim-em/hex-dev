/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

meta import HexPermGroup.Build.Bounded
import HexPermGroup.Build.Bounded

/-! Producer budget regressions: each exhausted resource, zero allowance,
exact reservation boundaries, and equality with the complete construction. -/

open Hex Hex.PermGroup
open Hex.PermGroup.Execution

private def swap : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def cycle : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩

private def allowance : Budget :=
  { points := 100000, pairs := 100000, sifts := 100000,
    certificates := 100000, images := 1000000 }

private def withLimit (w : Work) (r : Resource) (k : Nat) : Work := match r with
  | .nodes => { w with nodes := k }
  | .refinements => { w with refinements := k }
  | .sifts => { w with sifts := k }
  | .certificates => { w with certificates := k }
  | .points => { w with points := k }
  | .pairs => { w with pairs := k }
  | .images => { w with images := k }

#eval show IO Unit from do
  for S in ([#[swap, cycle], #[cycle, swap, cycle.inv, Perm.id 3], #[]] : List (Array (Perm 3))) do
    let used : Work ← match Group.buildWith allowance S with
      | .exhausted failure => throw (IO.userError s!"construction exhausted {repr failure.resource}")
      | .ok result meter =>
        unless checkChain S result.val.chain do throw (IO.userError "bounded chain rejected")
        let expected := Group.ofGenerators S
        unless result.val.order == expected.order do throw (IO.userError "bounded order differs")
        pure meter.used
    match Group.buildWith used S with
    | .exhausted _ => throw (IO.userError "exact construction allowance exhausted")
    | .ok _ meter =>
      unless meter.used == used do throw (IO.userError "construction accounting depends on surplus budget")
    for resource in [Resource.points, .pairs, .sifts, .certificates, .images] do
      if used.get resource > 0 then
        for cap in [0, used.get resource - 1] do
          let budget := withLimit allowance resource cap
          match Group.buildWith budget S with
          | .ok _ _ => throw (IO.userError s!"construction ignored {repr resource} limit")
          | .exhausted failure =>
            unless failure.resource == resource && failure.meter.used.get resource <= cap do
              throw (IO.userError "wrong construction exhaustion or exceeded allowance")

#eval show IO Unit from do
  match Group.buildWith { certificates := 1 } (#[] : Array (Perm 0)) with
  | .ok result meter =>
    unless result.val.order == 1 && meter.used.certificates == 1 do
      throw (IO.userError "degree-zero construction contract")
  | .exhausted _ => throw (IO.userError "degree-zero exact allowance exhausted")
  match Group.buildWith {} (#[] : Array (Perm 0)) with
  | .ok _ _ => throw (IO.userError "zero allowance allocated a chain node")
  | .exhausted failure =>
    unless failure.resource == Resource.certificates && failure.meter.used == ({} : Work) do
      throw (IO.userError "zero allowance performed construction work")
