/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

meta import HexPermGroup.Build.Bounded
import HexPermGroup.Build.Bounded
meta import HexPermGroup.Product.Bounded
import HexPermGroup.Product.Bounded
meta import HexPermGroup.Normal.Bounded
import HexPermGroup.Normal.Bounded
meta import HexPermGroup.Normal.SeriesMetered
import HexPermGroup.Normal.SeriesMetered

/-! Producer budget regressions: each exhausted resource, zero allowance,
exact reservation boundaries, and equality with the complete construction. -/

open Hex Hex.PermGroup
open Hex.PermGroup.Execution

private def swap : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def cycle : Perm 3 := ⟨#v[1, 2, 0], by decide, by decide⟩

private def allowance : Budget :=
  { nodes := 100000, points := 100000, pairs := 100000, sifts := 100000,
    certificates := 100000, images := 1000000, storage := 1000000 }

private def withLimit (w : Work) (r : Resource) (k : Nat) : Work := match r with
  | .nodes => { w with nodes := k }
  | .refinements => { w with refinements := k }
  | .sifts => { w with sifts := k }
  | .certificates => { w with certificates := k }
  | .points => { w with points := k }
  | .pairs => { w with pairs := k }
  | .images => { w with images := k }
  | .storage => { w with storage := k }

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
    for resource in [Resource.points, .pairs, .sifts, .certificates, .images, .storage] do
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

-- C₂ has two Schreier pairs, both identities. Its only suffix construction
-- is the trivial chain. These counts are derived from those operations,
-- independently of a prior metered run.
#eval show IO Unit from do
  let transposition : Perm 2 := ⟨#v[1, 0], by decide, by decide⟩
  let expected : Work :=
    { points := (2 * 1 + 1) + (2 * 0 + 1), pairs := 2, sifts := 2 * 2,
      certificates := 5 + 4 + 1 + 2 + 1,
      images := 114 + 4 + 2 + 2 * (6 + 6),
      storage := 108 + 48 + 48 + 1 + 3 * 2 }
  match Group.buildWith expected #[transposition] with
  | .exhausted failure => throw (IO.userError s!"C2 reservation boundary: {repr failure.resource}")
  | .ok group meter =>
    unless group.val.order == 2 && meter.used == expected do
      throw (IO.userError "C2 construction omitted or miscounted work")

#eval show IO Unit from do
  let transposition : Perm 2 := ⟨#v[1, 0], by decide, by decide⟩
  let G := Group.ofGenerators #[transposition, transposition]
  let H := Group.ofGenerators #[swap]
  let limits : ProductLimits := ⟨6, 7, allowance⟩
  match G.directProductWith { limits with degree := 4 } H with
  | .error (.degree 5 4) => pure ()
  | _ => throw (IO.userError "direct product omitted a declared fixed point")
  match G.directProductWith { limits with generators := 2 } H with
  | .error (.generators 3 2) => pure ()
  | _ => throw (IO.userError "direct product ignored raw generator multiplicities")
  match G.wreathProductWith { limits with degree := 5 } H (Nat.zero_lt_succ 1) with
  | .error (.degree 6 5) => pure ()
  | _ => throw (IO.userError "wreath product omitted a fixed block")
  match G.wreathProductWith { limits with generators := 6 } H (Nat.zero_lt_succ 1) with
  | .error (.generators 7 6) => pure ()
  | _ => throw (IO.userError "wreath generator count must be m*rG+rH")
  let two := Group.ofGenerators #[transposition]
  match two.directProductWith { limits with degree := 4, generators := 2 } two with
  | .ok (.ok result meter) =>
    unless result.val.order == 4 do throw (IO.userError "bounded C2 direct product")
    match Group.buildWith allowance result.val.generators with
    | .ok _ construction =>
      unless meter.used.images == construction.used.images + 12 &&
          meter.used.storage == construction.used.storage + 4 do
        throw (IO.userError "direct product reset its materialization meter")
    | _ => throw (IO.userError "direct product reference allowance")
  | _ => throw (IO.userError "direct product exact dimension boundary")
  match two.wreathProductWith { limits with degree := 4, generators := 3 } two (Nat.zero_lt_succ 1) with
  | .ok (.ok result meter) =>
    unless result.val.order == 8 do throw (IO.userError "bounded C2 wreath product")
    match Group.buildWith allowance result.val.generators with
    | .ok _ construction =>
      unless meter.used.images == construction.used.images + 30 &&
          meter.used.storage == construction.used.storage + 17 do
        throw (IO.userError "wreath product reset its materialization meter")
    | _ => throw (IO.userError "wreath product reference allowance")
  | _ => throw (IO.userError "wreath product exact dimension boundary")
  match two.directProductWith { limits with work := {} } two with
  | .ok (.exhausted failure) =>
    unless failure.resource == Resource.storage && failure.meter.used == ({} : Work) do
      throw (IO.userError "product allocated before its first reservation")
  | _ => throw (IO.userError "zero product allowance accepted")

#eval show IO Unit from do
  let H := Group.ofGenerators #[swap]
  let G := H.adjoin cycle
  let used ← match G.normalClosureWith allowance H (H.subgroup_adjoin cycle) with
    | .ok result meter =>
      unless result.group.order == 6 && !result.trace.isEmpty &&
          Normal.checkClosure G H result.group result.trace do
        throw (IO.userError "bounded normal closure lost its forced conjugate or replay")
      pure meter.used
    | .exhausted failure => throw (IO.userError s!"normal closure allowance: {repr failure.resource}")
  match G.normalClosureWith used H (H.subgroup_adjoin cycle) with
  | .ok _ meter =>
    unless meter.used == used do throw (IO.userError "normal closure depends on surplus allowance")
  | _ => throw (IO.userError "normal closure exact boundary")
  for resource in [Resource.points, .pairs, .sifts, .certificates, .images, .storage] do
    unless used.get resource > 0 do throw (IO.userError "normal closure did not exercise nested construction")
    for cap in [0, used.get resource - 1] do
      match G.normalClosureWith (withLimit allowance resource cap) H (H.subgroup_adjoin cycle) with
      | .ok _ _ => throw (IO.userError "normal closure ignored a cumulative limit")
      | .exhausted failure =>
        unless failure.resource == resource && failure.meter.used.get resource <= cap do
          throw (IO.userError "normal closure lost its stopping counters")
        if resource == Resource.points && cap == 0 then
          unless failure.meter.used.sifts > 0 && failure.meter.used.certificates > 0 do
            throw (IO.userError "normal closure reset its meter before the nested chain build")

#eval show IO Unit from do
  match Execution.run allowance (Build.bounded 0 (Nat.zero_le 3) #[swap, cycle]
      (by intro _ x hx; omega)) with
  | .ok result meter =>
    unless result.val.rebuilds > 0 && meter.used.pairs > 0 do
      throw (IO.userError "S3 regression did not exercise a discarded suffix rebuild")
  | .exhausted _ => throw (IO.userError "S3 rebuild allowance")

#eval show IO Unit from do
  let a : Perm 4 := ⟨#v[1, 0, 2, 3], by decide, by decide⟩
  let b : Perm 4 := ⟨#v[1, 2, 3, 0], by decide, by decide⟩
  let G := Group.ofGenerators #[a, b]
  match G.derivedWith allowance with
  | .ok result _ =>
    unless result.group.order == 12 && Derived.check G result.group result.certificate do
      throw (IO.userError "bounded S4 derived subgroup or replay")
  | .exhausted failure => throw (IO.userError s!"S4 derived allowance: {repr failure.resource}")
  for terms in [0, 1, 2, 3] do
    match G.derivedSeriesWithin allowance terms with
    | .ok result _ =>
      unless result.val.certificate.check G && result.val.certificate.terms <= terms &&
          result.val.answer? == (if terms == 3 then some true else none) do
        throw (IO.userError "derived term cap supplied an invalid prefix or premature answer")
    | .exhausted failure => throw (IO.userError s!"S4 series allowance: {repr failure.resource}")
  let used ← match G.derivedSeriesWithin allowance 3 with
    | .ok _ meter => pure meter.used
    | .exhausted _ => throw (IO.userError "S4 series allowance")
  match G.derivedSeriesWithin used 3 with
  | .ok result meter =>
    unless result.val.answer? == some true && meter.used == used do
      throw (IO.userError "derived series exact allowance changed its result")
  | _ => throw (IO.userError "derived series exact boundary")
  for resource in [Resource.nodes, .points, .pairs, .sifts, .certificates, .images, .storage] do
    unless used.get resource > 0 do throw (IO.userError "S4 did not exercise a derived resource")
    for cap in [0, used.get resource - 1] do
      match G.derivedSeriesWithin (withLimit allowance resource cap) 3 with
      | .ok _ _ => throw (IO.userError "derived series ignored its producer budget")
      | .exhausted failure =>
        unless failure.resource == resource && failure.meter.used.get resource <= cap do
          throw (IO.userError "derived series lost the failed resource")
