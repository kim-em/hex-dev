/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Dag
public import Std.Data.HashMap

public section

namespace Hex

instance {E : Type u} [Zero E] [DecidableEq E] : DecidableEq (RemainderStep E) := by
  intro a b
  cases a
  cases b
  simp only [RemainderStep.mk.injEq]
  infer_instance

instance {E : Type u} [Zero E] [DecidableEq E] : DecidableEq (SignedRemainderChain E) := by
  intro a b
  cases a
  cases b
  simp only [SignedRemainderChain.mk.injEq]
  infer_instance

instance {D : Type u} {E : Type v} {Ctx : Type w} [Zero D] [DecidableEq D]
    [DecidableEq E] [DecidableEq Ctx] : DecidableEq (TarskiCertificate D E Ctx) := by
  intro a b
  cases a
  cases b
  simp only [TarskiCertificate.mk.injEq]
  infer_instance

deriving instance DecidableEq for Matrix.RankCert
deriving instance DecidableEq for SignDet.System

instance {E : Type u} [Zero E] [DecidableEq E] : DecidableEq (SignDet.ReductionStep E) := by
  intro a b
  cases a
  cases b
  simp only [SignDet.ReductionStep.mk.injEq]
  infer_instance

instance {E : Type u} [Zero E] [DecidableEq E] : DecidableEq (SignDet.Reduction E) := by
  intro a b
  cases a
  cases b
  simp only [SignDet.Reduction.mk.injEq]
  infer_instance

instance {E : Type u} [Zero E] [DecidableEq E] : DecidableEq (SignDet.QueryReduction E) := by
  intro a b
  cases a
  cases b
  simp only [SignDet.QueryReduction.mk.injEq]
  infer_instance

instance {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx] :
    DecidableEq (SignDet.Node E Ctx) := by
  intro a b
  cases a with
  | mk ca pa la ua qa na sa ma ra da ba =>
    cases b with
    | mk cb pb lb ub qb nb sb mb rb db bb =>
      by_cases h : na = nb
      · subst nb
        by_cases hs : sa = sb
        · subst sb
          simp only [SignDet.Node.mk.injEq, heq_eq_eq]
          infer_instance
        · exact isFalse fun he => hs (by cases he; rfl)
      · exact isFalse fun he => h (by cases he; rfl)

instance {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx] :
    DecidableEq (SignDet.Dag.Entry E Ctx) := by
  intro a b
  cases a
  cases b
  simp only [SignDet.Dag.Entry.mk.injEq]
  infer_instance

namespace SignDet.Dag

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [Hashable E] [Hashable Ctx]

/-- Hashing narrows the search; exact equality still compares every node field,
including all witnesses and literal context bindings. A collision never licenses
sharing. Child indices distinguish nodes with different descendants. -/
instance : Hashable (Entry E Ctx) where
  hash e := hash (e.node.context, e.node.queries.map (·.toArray), e.node.size,
    e.node.system.columns.toArray, e.children)

/-- Construction state for bottom-up hash consing. This is producer state, not
trusted checker evidence. The graph checker validates its output independently. -/
structure Encoder (E : Type u) (Ctx : Type v) [Zero E] [DecidableEq E]
    [DecidableEq Ctx] [Hashable E] [Hashable Ctx] where
  entries : Array (Entry E Ctx) := #[]
  indices : Std.HashMap (Entry E Ctx) Nat := {}

/-- Retain the first exact occurrence and its stable index. -/
@[expose] def Encoder.insert (state : Encoder E Ctx) (entry : Entry E Ctx) : Encoder E Ctx × Nat :=
  match state.indices[entry]? with
  | some i => (state, i)
  | none =>
    let i := state.entries.size
    (⟨state.entries.push entry, state.indices.insert entry i⟩, i)

/-- Left-to-right postorder traversal. The parent is interned only after both
children, so generated child references point into the preceding prefix. -/
@[expose] def encodeFrom (state : Encoder E Ctx) : Replay E Ctx → Encoder E Ctx × Nat
  | .leaf n => state.insert ⟨n, none⟩
  | .split n l r =>
    let (state, left) := encodeFrom state l
    let (state, right) := encodeFrom state r
    state.insert ⟨n, some (left, right)⟩

/-- Encode an arbitrary supplied replay tree, sharing exactly repeated literal
nodes with the same child references. This does not validate the input or attach
an acceptance proof; use `replay?` to check the resulting graph. Hash consing
visits every input occurrence and retains the first occurrence of each entry.
It does not serialize coefficient values or lower-level coefficient proofs. -/
@[expose] def encode (tree : Replay E Ctx) : Dag E Ctx :=
  let (state, root) := encodeFrom {} tree
  ⟨state.entries, root⟩

end SignDet.Dag

end Hex
