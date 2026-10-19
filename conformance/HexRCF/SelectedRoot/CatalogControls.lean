/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Catalog
public import HexRCF.SelectedRoot.CatalogBytes

public section

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

/-- Change the lower endpoint while retaining the old graph domain. -/
def changedEndpoint : Serialized :=
  ⟨Data.parent.signature, .array (.cons (.number 1) (.cons
    (match CatalogData.j71 with
      | .array (.cons context (.cons polynomial (.cons _ (.cons upper rest)))) =>
        .array (.cons context (.cons polynomial (.cons upper (.cons upper rest))))
      | other => other) .nil))⟩

/-- Retain the original predecessor explicitly inside a packet naming the rational base. -/
def staleContext : Serialized :=
  ⟨Data.base.signature, .array (.cons (.number 1) (.cons
    (match CatalogData.j71 with
      | .array (.cons _ rest) => .array (.cons
          (.array (.cons (.number 1) (.cons Data.parent.signature.literal.toJson .nil))) rest)
      | other => other) .nil))⟩

/-- Compiled diagnostics exercise the catalog reader; they are not proof evidence. -/
private def catalogRejected (raw : Serialized) (expected : String) : Bool :=
  match (Tower.Catalog.empty Data.registry).restoreRootBytes raw.writeBytes with
  | .error message => message == expected
  | .ok _ => false

private def catalogAccepted : Bool :=
  match (Tower.Catalog.empty Data.registry).restoreRootBytes CatalogByteData.literal with
  | .error _ => false
  | .ok root => root.parent.signature == Data.parent.signature &&
      root.root.writeBytes == CatalogByteData.literal

#guard (match CatalogData.j71 with
  | .array (.cons _ (.cons _ (.cons lower (.cons upper _)))) => lower != upper
  | _ => false)
#guard catalogAccepted
#guard catalogRejected staleContext "root descriptor predecessor mismatch"
#guard catalogRejected ⟨Data.parent.signature, (Tower.RootSet.all (parent := Data.parent)).data⟩
  "unknown root kind"
#guard catalogRejected changedEndpoint "graph context or domain mismatch"

#print axioms truncatedCheck
#print axioms truncatedRejected
#print axioms byteLimit
#print axioms byteLimitRejected
#print axioms staleBinding
#print axioms staleRejected
#print axioms setRejected
end Hex.RCF.SelectedRootTests.CatalogControls
