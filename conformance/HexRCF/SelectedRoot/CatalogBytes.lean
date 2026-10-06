/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Catalog
import HexRCF.SelectedRoot.CatalogByteData
import HexRealClosure.RootBytes

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.SelectedRootTests
open Hex.RCF.SelectedRootTests.CatalogByteData
namespace Hex.RCF.SelectedRootTests.CatalogBytes
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem packetWritten : CatalogData.packet.writeBytes = literal := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [Codec.Json.Value.writeBytes_toList, Codec.Json.Value.tokensLoop_spec]
  decide +kernel

theorem written : CatalogSource.selected.write.writeBytes = literal := by
  change (Serialized.codec.encode CatalogSource.selected.write).writeBytes = literal
  exact (congrArg Codec.Json.Value.writeBytes CatalogPacket.written).trans packetWritten

set_option maxRecDepth 32768 in
theorem size : literal.size = 2911 := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem bound : Codec.checkBytes {} literal = .ok () := by
  unfold Codec.checkBytes
  simp only [Codec.forIn_data, ← Array.forIn_toList]
  decide +kernel

theorem restoreParsed {registry : BaseContext.Registry} (catalog : Catalog registry)
    (input : ByteArray) (limits : Codec.Limits) (raw : Serialized)
    (decoded : Serialized.readBytes input limits = .ok raw) :
    catalog.restoreRootBytes input limits = catalog.restoreRoot raw := by
  unfold Catalog.restoreRootBytes
  rw [decoded]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem accepted : (Catalog.empty Data.registry).restoreRootBytes literal =
    .ok ⟨Data.parent, CatalogSource.selected⟩ := by
  have bounded : Codec.checkBytes {} CatalogSource.selected.write.writeBytes = .ok () :=
    (congrArg (Codec.checkBytes {}) written).trans bound
  have parser : Serialized.readBytes literal {} = .ok CatalogSource.selected.write :=
    (congrArg (fun bytes => Serialized.readBytes bytes {}) written).symm.trans
      (Serialized.readBytes_write CatalogSource.selected.write {} bounded)
  exact (restoreParsed (Catalog.empty Data.registry) literal {} CatalogSource.selected.write
    parser).trans CatalogSource.fresh

theorem source : ∃ root : PackedRoot Data.registry,
    (Catalog.empty Data.registry).restoreRootBytes literal = .ok root ∧
    ∃ original : Model root.parent ℝ,
      (root.root.denote original)^2 = Real.sqrt 2 ∧
      1 < root.root.denote original ∧ root.root.denote original < 2 :=
  ⟨⟨Data.parent, CatalogSource.selected⟩, accepted, Data.original, CatalogSource.source⟩

theorem exists_nested : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  obtain ⟨root, _, original, truth⟩ := source
  exact ⟨root.root.denote original, truth⟩

#print axioms source
#print axioms exists_nested
#print axioms written
#print axioms bound
#print axioms accepted
end Hex.RCF.SelectedRootTests.CatalogBytes
