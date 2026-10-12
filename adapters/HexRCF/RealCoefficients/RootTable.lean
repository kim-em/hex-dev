/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SectionReplay
public import HexSignDet.RootList
public import HexSignDet.DescriptorOperations
public section
namespace Hex.RCF.RealCoefficients.RootTable
open Hex Hex.SignDet
variable {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
variable [targetOne : One E] [targetAdd : Add E] [targetSub : Sub E]
variable [targetMul : Mul E] [targetNat : NatCast E]
/-- Finite checked data with the actual coefficient operations as indices. -/
structure Result (sign : E → Int) (binding : Ctx) (p : DensePoly E) (lo hi : Endpoint E) where
  tree : SignDet.Replay E Ctx
  checked : tree.check sign binding p lo hi
    ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full []).queries = true
  roots : List (Descriptor E Ctx sign binding)
  extracted : Descriptor.rootsFrom sign binding ⟨binding, p, lo, hi, [], []⟩ tree
    (tree.table checked).rows.toList = .ok roots

/-- Shared full-table extraction; the constant branch retains literal behavior. -/
@[expose] def extract (sign : E → Int) (binding : Ctx) (p : DensePoly E)
    (lo hi : Endpoint E) (tree : SignDet.Replay E Ctx)
    (checked : tree.check sign binding p lo hi
      ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full []).queries = true) :=
  let raw : RawDescriptor E Ctx := ⟨binding, p, lo, hi, [], []⟩
  if positive : 0 < p.natDegree then
    Descriptor.rootsFromTable raw tree positive rfl checked
      (tree.table checked).rows.toList (fun _ member => member)
  else Descriptor.rootsFrom sign binding raw tree (tree.table checked).rows.toList

theorem extract_eq (sign : E → Int) (binding : Ctx) (p : DensePoly E)
    (lo hi : Endpoint E) (tree : SignDet.Replay E Ctx)
    (checked : tree.check sign binding p lo hi
      ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full []).queries = true) :
    extract sign binding p lo hi tree checked =
      Descriptor.rootsFrom sign binding ⟨binding, p, lo, hi, [], []⟩ tree
        (tree.table checked).rows.toList := by
  by_cases positive : 0 < p.natDegree
  · simp only [extract, positive, ↓reduceDIte]
    exact Descriptor.rootsFromTable_eq _ _ _ _ _ _ _
  · simp only [extract, positive, ↓reduceDIte]

/-- Restore one supplied graph with original guard preflight. -/
@[expose] def read (value : ValueCodec E) (ctx : ValueCodec Ctx) (sign : E → Int)
    (binding : Ctx) (guards : List E) (p : DensePoly E) (lo hi : Endpoint E)
    (graph : Codec.Json) : Except Hex.RCF.RealCoefficients.Replay.Error
      (Result sign binding p lo hi) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let dag ← match Codec.readGraph value ctx binding p lo hi graph with
    | .error _ => .error .evidence
    | .ok dag => .ok dag
  let tree ← match dag.replay? sign binding p lo hi
      ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full []).queries with
    | none => .error .evidence
    | some tree => .ok tree
  match output : extract sign binding p lo hi tree.val tree.property with
  | .error _ => .error .evidence
  | .ok roots => .ok ⟨tree.val, tree.property, roots,
      (extract_eq sign binding p lo hi tree.val tree.property).symm.trans output⟩

/-- Retain data and change only proof indices through equal predecessor operations. -/
@[expose] def changeOps (one : One E) (add : Add E) (sub : Sub E)
    (mul : Mul E) (nat : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : nat = targetNat)
    (sign : E → Int) (binding : Ctx) (p : DensePoly E) (lo hi : Endpoint E)
    (source : @Result E Ctx _ _ _ one add sub mul nat sign binding p lo hi) :
    @Result E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat sign binding p lo hi :=
  let tree := source.tree
  let roots := source.roots.map (@Descriptor.changeOps E Ctx _ _ _
    targetOne targetAdd targetSub targetMul targetNat one add sub mul nat ho ha hs hm hn sign binding)
  let checked : @SignDet.Replay.check E Ctx _ _ targetOne targetAdd targetSub targetMul targetNat _
      sign binding p lo hi
      (@RawDescriptor.queries E Ctx _ _ targetNat targetMul
        ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full [])) tree = true := by
    have h := source.checked
    change @SignDet.Replay.check E Ctx _ _ one add sub mul nat _ sign binding p lo hi
      (@RawDescriptor.queries E Ctx _ _ nat mul
        ((⟨binding, p, lo, hi, [], []⟩ : RawDescriptor E Ctx).full [])) tree = true at h
    cases ho
    cases ha
    cases hs
    cases hm
    cases hn
    exact h
  @Result.mk E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat
    sign binding p lo hi tree checked roots (by
    cases ho
    cases ha
    cases hs
    cases hm
    cases hn
    have same : roots = source.roots := by
      dsimp only [roots]
      induction source.roots with
      | nil => rfl
      | cons root rest ih =>
        simp only [List.map_cons]
        rw [Descriptor.changeOps_self]
        exact congrArg (List.cons root) ih
    rw [same]
    exact source.extracted)

theorem changeOps_self (sign : E → Int) (binding : Ctx) (p : DensePoly E) (lo hi : Endpoint E)
    (result : Result sign binding p lo hi) :
    changeOps targetOne targetAdd targetSub targetMul targetNat rfl rfl rfl rfl rfl
      sign binding p lo hi result = result := by
  have same : result.roots.map (Descriptor.changeOps targetOne targetAdd targetSub targetMul
      targetNat rfl rfl rfl rfl rfl sign binding) = result.roots := by
    induction result.roots with
    | nil => rfl
    | cons root rest ih =>
      simp only [List.map_cons]
      rw [Descriptor.changeOps_self]
      exact congrArg (List.cons root) ih
  cases result
  unfold changeOps
  simp only at same
  simp only [same]

/-- Supplied equal operations are used during replay and extraction, then the
checked result returns with canonical proof indices. -/
@[expose] def readWith (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (one : One E) (add : Add E) (sub : Sub E) (mul : Mul E) (nat : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : nat = targetNat)
    (sign : E → Int) (binding : Ctx) (guards : List E)
    (p : DensePoly E) (lo hi : Endpoint E) (graph : Codec.Json) :
    Except Hex.RCF.RealCoefficients.Replay.Error
      (@Result E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat sign binding p lo hi) :=
  (@read E Ctx _ _ _ one add sub mul nat value ctx sign binding guards p lo hi graph).map
    (@changeOps E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat
      one add sub mul nat ho ha hs hm hn sign binding p lo hi)

theorem readWith_eq (value : ValueCodec E) (ctx : ValueCodec Ctx)
    (one : One E) (add : Add E) (sub : Sub E) (mul : Mul E) (nat : NatCast E)
    (ho : one = targetOne) (ha : add = targetAdd) (hs : sub = targetSub)
    (hm : mul = targetMul) (hn : nat = targetNat)
    (sign : E → Int) (binding : Ctx) (guards : List E)
    (p : DensePoly E) (lo hi : Endpoint E) (graph : Codec.Json) :
    @readWith E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat value ctx
      one add sub mul nat ho ha hs hm hn sign binding guards p lo hi graph =
      @read E Ctx _ _ _ targetOne targetAdd targetSub targetMul targetNat
        value ctx sign binding guards p lo hi graph := by
  cases ho
  cases ha
  cases hs
  cases hm
  cases hn
  unfold readWith
  cases read value ctx sign binding guards p lo hi graph with
  | error error => rfl
  | ok result =>
    change Except.ok (changeOps _ _ _ _ _ rfl rfl rfl rfl rfl sign binding p lo hi result) = _
    rw [changeOps_self]

end Hex.RCF.RealCoefficients.RootTable
