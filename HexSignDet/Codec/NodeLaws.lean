/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Node
public import HexSignDet.Codec.EvidenceLaws
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Node
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.SignDet.Codec
open Lean

/-- A size-indexed traversal only requires roundtrips for its actual entries. -/
theorem read_vector_of (encode : α → Json) (read : Json → Except String α)
    (a : Vector α n) (h : ∀ x ∈ a.toList, read (encode x) = .ok x) :
    vector n read (array encode a.toArray) = .ok a := by
  have hm : (a.toArray.map encode).mapM read = .ok a.toArray := by
    rw [Array.mapM_eq_mapM_toList]
    have hl := read_list_of encode read a.toList h
    change Array.toList <$> (a.toList.toArray.map encode).mapM read = .ok a.toList at hl
    rw [Array.toList_mapM] at hl
    simpa [Vector.toList, Functor.map, Except.map] using
      congrArg (Functor.map List.toArray) hl
  simp [vector, tuple, array, Json.getArr?, bind, Except.bind, pure, Except.pure,
    a.size_toArray, hm]

/-- Lists embedded in a dimensioned system preserve their literal order. -/
theorem read_sizedList {α : Type} [ToJson α] [FromJson α]
    (h : ∀ x : α, fromJson? (toJson x) = .ok x) (xs : List α)
    (size : xs.length = n) :
    Vector.toList <$> vector n (fromJson? (α := α)) (toJson xs) = .ok xs := by
  subst n
  have hv := read_vector toJson fromJson? h (⟨xs.toArray, by simp⟩ : Vector α xs.length)
  simpa [array, toJson, List.toJson, Array.toJson, Functor.map, Except.map] using
    congrArg (Functor.map Vector.toList) hv

/-- Parsing preserves the six literal system fields whenever its row and
column words have the declared arity. No matrix identity is assumed. -/
theorem read_system (s : System n)
    (rows : ∀ x ∈ s.rows.toList, x.length = arity)
    (columns : ∀ x ∈ s.columns.toList, x.length = arity) :
    readSystem n arity (system s) = .ok s := by
  have hr := read_vector_of toJson
    (fun j => Vector.toList <$> vector arity (fromJson? (α := Nat)) j) s.rows
    (fun x hx => read_sizedList read_nat x (rows x hx))
  have hc := read_vector_of toJson
    (fun j => Vector.toList <$> vector arity (fromJson? (α := Int)) j) s.columns
    (fun x hx => read_sizedList read_int x (columns x hx))
  have hi := read_vector (n := n) toJson fromJson? read_int
  simp [readSystem, system, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    show toJson s.rows.toArray = array toJson s.rows.toArray from rfl,
    show toJson s.columns.toArray = array toJson s.columns.toArray from rfl,
    show toJson s.counts.toArray = array toJson s.counts.toArray from rfl,
    show toJson s.values.toArray = array toJson s.values.toArray from rfl,
    hr, hc, hi, read_matrix]

/-- Bounded index vectors and the complete inverse block roundtrip literally.
The rank bound is a parser shape condition, not a rank-correctness premise. -/
theorem read_basis (b : Matrix.RankCert Int n m) (rows : b.rank ≤ n) (cols : b.rank ≤ m) :
    readBasis n m (basis b) = .ok b := by
  have hr := read_vector (fun i : Fin n => toJson i.val) (index n) read_index b.rows
  have hc := read_vector (fun i : Fin m => toJson i.val) (index m) read_index b.cols
  have er : toJson (b.rows.toArray.map Fin.val) =
      array (fun i : Fin n => toJson i.val) b.rows.toArray := by
    simp [toJson, Array.toJson, array, Array.map_map, Function.comp_def]
  have ec : toJson (b.cols.toArray.map Fin.val) =
      array (fun i : Fin m => toJson i.val) b.cols.toArray := by
    simp [toJson, Array.toJson, array, Array.map_map, Function.comp_def]
  simp [readBasis, basis, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    Nat.not_lt.mpr rows, Nat.not_lt.mpr cols, er, ec, hr, hc, read_matrix]

/-- Optional evidence needs a roundtrip only when it is present. -/
theorem read_option_of (encode : α → Json) (read : Json → Except String α)
    (a : Option α) (h : ∀ x ∈ a, read (encode x) = .ok x) :
    readOption read (option encode a) = .ok a := by
  cases a <;> simp_all [readOption, option, Json.getArr?, bind, Except.bind, pure,
    Except.pure, Functor.map, Except.map]

variable {E Ctx : Type} [Zero E] [DecidableEq E]

/-- All eleven node fields roundtrip under the parser's structural bounds.
Arithmetic identities, root counts and support completeness are not premises. -/
theorem read_node (value : ValueCodec E) (context : ValueCodec Ctx)
    (hv : value.Lawful) (hc : context.Lawful) (n : Node E Ctx)
    (rows : ∀ x ∈ n.system.rows.toList, x.length = n.queries.length)
    (columns : ∀ x ∈ n.system.columns.toList, x.length = n.queries.length)
    (rankRows : n.basis.rank ≤ n.size) (rankCols : n.basis.rank ≤ n.system.positive.length)
    (reductions : ∀ r ∈ n.reductions.toList, ∀ t ∈ r, ∀ s ∈ t.steps,
      s.index < n.queries.length)
    (prepared : ∀ t ∈ n.preparation, ∀ s ∈ t.steps, s.index < n.queries.length) :
    readNode value context (node value context n) = .ok n := by
  have hr := read_vector_of (option (reduction value))
    (readOption (readReduction value n.queries.length)) n.reductions
    (fun r hr => read_option_of _ _ r
      (fun t ht => read_reduction value hv t (reductions r hr t ht)))
  have hp := read_option_of (preparation value)
    (readPreparation value n.queries.length) n.preparation
    (fun t ht => read_preparation value hv t (prepared t ht))
  have hm := read_vector _ _ (read_tarski value context hv hc) n.moments
  have ctx := hc
  unfold ValueCodec.Lawful at ctx
  simp [readNode, node, tuple, Json.getArr?, bind, Except.bind, pure, Except.pure,
    ctx, read_poly value hv, read_endpoint value hv, read_list _ _ (read_poly value hv),
    read_system n.system rows columns, hr, hp, hm, read_basis n.basis rankRows rankCols]

end Hex.SignDet.Codec
