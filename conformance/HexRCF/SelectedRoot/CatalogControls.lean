/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Catalog
import HexRCF.SelectedRoot.CatalogBytes

open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet Hex.RCF.SelectedRootTests
namespace Hex.RCF.SelectedRootTests.CatalogControls

def stale : Serialized := ⟨Data.base.signature, CatalogSource.selected.data⟩
set_option maxRecDepth 32768 in
theorem staleBinding : stale.binding ≠ Data.parent.signature := by decide +kernel

theorem staleRejected : Data.parent.readRootPacket stale =
    .error "root predecessor mismatch" :=
  Data.parent.readRoot_stale stale staleBinding

theorem setRejected : Data.parent.readRoot (Tower.RootSet.all (parent := Data.parent)).data =
    .error "unknown root kind" := Data.parent.readRootSet_asRoot .all

theorem parsedFailure {registry : BaseContext.Registry} (catalog : Catalog registry)
    (input : ByteArray) (limits : Codec.Limits) (message : String)
    (failed : Serialized.readBytes input limits = .error message) :
    catalog.restoreRootBytes input limits = .error message := by
  unfold Catalog.restoreRootBytes
  rw [failed]

theorem lexicalFailure (input : ByteArray) (limits : Codec.Limits) (message : String)
    (failed : Codec.checkBytes limits input = .error message) :
    Serialized.readBytes input limits = .error message := by
  unfold Serialized.readBytes ValueCodec.decodeBytes Codec.parse
  rw [failed]
  rfl

set_option maxRecDepth 32768 in
theorem byteLimit : Codec.checkBytes {bytes := 0} CatalogByteData.literal =
    .error "certificate byte limit exceeded" := by decide +kernel

theorem byteLimitRejected : (Catalog.empty Data.registry).restoreRootBytes
    CatalogByteData.literal {bytes := 0} = .error "certificate byte limit exceeded" :=
  parsedFailure (Catalog.empty Data.registry) CatalogByteData.literal {bytes := 0} _
    (lexicalFailure CatalogByteData.literal {bytes := 0} _ byteLimit)

def truncated : ByteArray := ⟨⟨CatalogByteData.t0.take 2909⟩⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem truncatedCheck : Codec.checkBytes {} truncated =
    .error "truncated certificate syntax" := by
  unfold Codec.checkBytes
  simp only [Codec.forIn_data, ← Array.forIn_toList]
  decide +kernel

theorem truncatedRejected : (Catalog.empty Data.registry).restoreRootBytes truncated {} =
    .error "truncated certificate syntax" :=
  parsedFailure (Catalog.empty Data.registry) truncated {} _
    (lexicalFailure truncated {} _ truncatedCheck)

#print axioms truncatedCheck
#print axioms truncatedRejected
#print axioms byteLimit
#print axioms byteLimitRejected
#print axioms staleBinding
#print axioms staleRejected
#print axioms setRejected
end Hex.RCF.SelectedRootTests.CatalogControls
