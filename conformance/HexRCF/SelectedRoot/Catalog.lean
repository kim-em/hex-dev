/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.CatalogSource
import HexRCF.SelectedRoot.CatalogData

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.SelectedRootTests
namespace Hex.RCF.SelectedRootTests.Catalog
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem treeLeaf : Frozen.tree = .leaf Frozen.tree.node := by
  have shape : (match Frozen.tree with
      | .leaf _ => true | .split _ _ _ => false) = true := by decide +kernel
  cases he : Frozen.tree with
  | leaf node => rfl
  | split node left right => simp only [he, Bool.false_eq_true] at shape

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem frame : rootData Data.parent.codec Upper.root = CatalogData.j71 := by
  let : Hashable Data.parent.Value := ⟨fun a => hash (Data.parent.codec.encode a)⟩
  let : Hashable Signature := ⟨fun _ => 0⟩
  unfold rootData
  dsimp only
  have evidence : Upper.root.evidence = Frozen.tree := Descriptor.ofChecked_evidence _ _ _ _ _
  rw [evidence, treeLeaf]
  erw [Dag.encode_leaf]
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem written : Serialized.codec.encode CatalogSource.selected.write =
    CatalogData.packet := by
  have data : (Data.parent.adjoin Upper.root).frame.toJson = rootData Data.parent.codec Upper.root :=
    Literal.toJson_ofJson _ _ (Data.parent.adjoin Upper.root).encoded
  simp only [CatalogSource.selected, Root.write, Root.data, Serialized.codec, data]
  erw [frame]
  decide +kernel

theorem decoded : Serialized.codec.decode CatalogData.packet =
    .ok CatalogSource.selected.write := by
  rw [← written]
  exact Serialized.codec_lawful _

def read : Except String (PackedRoot Data.registry) :=
  match Serialized.codec.decode CatalogData.packet with
  | .error message => .error message
  | .ok raw => (Catalog.empty Data.registry).restoreRoot raw

theorem accepted : read = .ok ⟨Data.parent, CatalogSource.selected⟩ := by
  simp only [read, decoded, bind, Except.bind, CatalogSource.fresh]

theorem supplied : ∃ raw,
    Serialized.codec.decode CatalogData.packet = .ok raw ∧
    (Catalog.empty Data.registry).restoreRoot raw = .ok ⟨Data.parent, CatalogSource.selected⟩ ∧
    (CatalogSource.selected.denote Data.original)^2 = Real.sqrt 2 ∧
    1 < CatalogSource.selected.denote Data.original ∧
    CatalogSource.selected.denote Data.original < 2 :=
  ⟨_, decoded, CatalogSource.fresh, CatalogSource.source⟩

#print axioms accepted
#print axioms supplied
#print axioms treeLeaf
#print axioms frame
#print axioms written
#print axioms decoded
end Hex.RCF.SelectedRootTests.Catalog
