/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.PackingReplay
import HexRealClosure.RootBytes
import HexRealClosureMathlib.TowerRoots

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.SelectedRootTests.CatalogSource

def selected : Tower.Root Data.parent :=
  .selected Upper.root (Data.parent.adjoin Upper.root) rfl

theorem fresh : (Tower.Catalog.empty Data.registry).restoreRoot selected.write =
    .ok ⟨Data.parent, selected⟩ := by
  let base : BaseContext.PackedContext Data.registry := .pack (BaseContext.rational Data.registry)
  let suffix : Tower.Suffix (Tower.Context.ofBase base) := .root Data.lower .nil
  have available : (BaseContext.Catalog.empty Data.registry).read base.signature = some base := by
    apply BaseContext.Catalog.read_self
    exact BaseContext.Catalog.lookup_rational _
  obtain ⟨⟨context, binding⟩, decoded, same⟩ := Tower.Catalog.reconstruct_suffix
    (BaseContext.Catalog.empty Data.registry) base available suffix
  have same : context = Data.parent := same.trans Data.parent_eq
  cases same
  have signature : suffix.context.signature = Data.parent.signature :=
    congrArg Tower.Context.signature Data.parent_eq
  generalize hkey : suffix.context.signature = key at binding decoded
  have key_eq : key = Data.parent.signature := hkey.symm.trans signature
  cases key_eq
  simp [Tower.Catalog.empty, Tower.Catalog.restoreRoot, Tower.Root.write, decoded,
    Data.parent.readRoot_data,
    bind, Except.bind, pure, Except.pure]

theorem denote : selected.denote Data.original =
    Upper.context.rootValue Data.original.value Data.original.zero_iff
      Data.original.one Data.original.add Data.original.sub Data.original.mul
      Data.original.nat Data.original.sign := by
  rw [Tower.Root.denote_selection]
  rfl

theorem source :
    (selected.denote Data.original)^2 = Real.sqrt 2 ∧
      1 < selected.denote Data.original ∧ selected.denote Data.original < 2 := by
  have truth := (SelectedFormula.row_spec Data.original Upper.values [] Upper.schema
    Upper.context Controls.packet true (Packing.checked PackingReplay.facts
      PackingReplay.accepted)).mp rfl
  rw [← denote] at truth
  exact (Source.schema_real _).mp truth

#print axioms fresh
#print axioms source
end Hex.RCF.SelectedRootTests.CatalogSource
