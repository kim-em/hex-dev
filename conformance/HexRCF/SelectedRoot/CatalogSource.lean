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

private theorem castBase {left right : Tower.Context registry} (same : left = right)
    (origin : Tower.Origin left) : (same ▸ origin).base = origin.base := by
  cases same
  rfl

private theorem originBase : Data.parent.origin.base =
    BaseContext.PackedContext.pack (BaseContext.rational Data.registry) := by
  simp only [Data.parent, Tower.Context.origin, Tower.Chain.origin, castBase]
  rfl

theorem fresh : (Tower.Catalog.empty Data.registry).restoreRoot selected.write =
    .ok ⟨Data.parent, selected⟩ := by
  have available : (BaseContext.Catalog.empty Data.registry).read
      Data.parent.origin.base.signature = some Data.parent.origin.base := by
    rw [originBase]
    apply BaseContext.Catalog.read_self
    exact BaseContext.Catalog.lookup_rational _
  exact Tower.Catalog.restoreRoot_origin (BaseContext.Catalog.empty Data.registry)
    Data.parent available selected

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
