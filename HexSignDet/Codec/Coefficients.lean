/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.GraphLaws
import Std.Data.HashMap.Lemmas

public section

namespace Hex.SignDet.Codec.Coefficients

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- Stored coefficients in wire order, including zero scalars and duplicates.
This traversal does not perform coefficient arithmetic or sign searches. -/
@[expose] def poly (p : DensePoly E) : List E := p.toArray.toList

@[expose] def endpoint : Endpoint E → List E
  | .finite x => [x]
  | _ => []

@[expose] def remainder (s : RemainderStep E) : List E :=
  [s.leftScale] ++ poly s.quotient ++ [s.rightScale]

@[expose] def terminal (t : E × DensePoly E) : List E := [t.1] ++ poly t.2

@[expose] def chain (c : SignedRemainderChain E) : List E :=
  c.chain.toList.flatMap poly ++ remainder c.initial ++
    c.steps.toList.flatMap remainder ++ c.terminal.toList.flatMap terminal

@[expose] def tarski (c : TarskiCertificate E E Ctx) : List E :=
  poly c.head ++ poly c.queryPoly ++ endpoint c.lower ++ endpoint c.upper ++
    chain c.squarefree ++ chain c.remainders

@[expose] def step (s : ReductionStep E) : List E := poly s.next ++ remainder s.witness

@[expose] def reduction (r : Reduction E) : List E := r.steps.flatMap step ++ poly r.result

@[expose] def preparation (r : QueryReduction E) : List E := r.steps.flatMap step

@[expose] def node (n : Node E Ctx) : List E :=
  poly n.head ++ endpoint n.lower ++ endpoint n.upper ++ n.queries.flatMap poly ++
    n.moments.toList.flatMap tarski ++
    n.reductions.toList.flatMap (fun r => r.toList.flatMap reduction) ++
    n.preparation.toList.flatMap preparation

/-- Every serialized entry is included, even when it is not reachable from
the selected root. Child references and integer matrices contain no `E`. -/
@[expose] def graph (d : Dag E Ctx) : List E := d.entries.toList.flatMap (fun e => node e.node)

end Hex.SignDet.Codec.Coefficients

namespace Hex.SignDet

/-- A partial reader roundtrips the specified finite collection of literals. -/
@[expose] def ValueCodec.Covers (value : ValueCodec E) (xs : List E) : Prop :=
  ∀ x ∈ xs, value.decode (value.encode x) = .ok x

namespace ValueCodec

@[simp] theorem covers_nil (value : ValueCodec E) : value.Covers [] := by
  simp [Covers]

@[simp] theorem covers_cons (value : ValueCodec E) (x : E) (xs : List E) :
    value.Covers (x :: xs) ↔ value.decode (value.encode x) = .ok x ∧ value.Covers xs := by
  simp [Covers]

@[simp] theorem covers_append (value : ValueCodec E) (xs ys : List E) :
    value.Covers (xs ++ ys) ↔ value.Covers xs ∧ value.Covers ys := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append_left _ hx),
      fun y hy => h y (List.mem_append_right _ hy)⟩
  · rintro ⟨hx, hy⟩ x h
    exact (List.mem_append.mp h).elim (hx x) (hy x)

@[simp] theorem covers_flatMap (value : ValueCodec E) (f : α → List E) (xs : List α) :
    value.Covers (xs.flatMap f) ↔ ∀ x ∈ xs, value.Covers (f x) := by
  simp only [Covers, List.mem_flatMap]
  constructor
  · intro h x hx y hy
    exact h y ⟨x, hx, hy⟩
  · intro h y hy
    obtain ⟨x, hx, hy⟩ := hy
    exact h x hx y hy

theorem Lawful.covers {value : ValueCodec E} (h : value.Lawful) (xs : List E) :
    value.Covers xs := fun x _ => h x

end ValueCodec
end Hex.SignDet

namespace Hex.SignDet.Dag

/-- Hash-consing a single leaf stores that literal node at index zero.
The proof uses the empty-map law, without evaluating a native hash table. -/
theorem encode_leaf {E Ctx : Type} [Zero E] [DecidableEq E] [DecidableEq Ctx]
    [Hashable E] [Hashable Ctx] (n : Node E Ctx) :
    encode (.leaf n) = ⟨#[⟨n, none⟩], 0⟩ := by
  simp [encode, encodeFrom, Encoder.insert]

end Hex.SignDet.Dag
