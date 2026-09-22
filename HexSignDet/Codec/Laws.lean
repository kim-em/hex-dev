/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Basic
import all HexSignDet.Codec.Basic
import all Lean.Data.Json.Basic
import all Lean.Data.Json.FromToJson.Basic

public section

namespace Hex.SignDet
open Lean

/-- A literal value codec preserves the entire input value. This property is
needed for encoding roundtrips, not for soundness of independent replay. -/
@[expose] def ValueCodec.Lawful (codec : ValueCodec α) : Prop :=
  ∀ x, codec.decode (codec.encode x) = .ok x

namespace Codec

@[simp] theorem read_nat (n : Nat) : fromJson? (toJson n) = .ok n := by
  rfl

@[simp] theorem read_int (n : Int) : fromJson? (toJson n) = .ok n := by
  rfl

end Codec

theorem ValueCodec.nat_lawful : nat.Lawful := Codec.read_nat

theorem ValueCodec.rat_lawful : rat.Lawful := by
  intro q
  simp [rat, Json.getArr?, bind, Except.bind, pure, Except.pure, Codec.read_int, Codec.read_nat,
    q.den_nz, Rat.mkRat_self]

namespace Codec

/-- Element roundtrips lift through the actual ordered array decoder. -/
theorem read_array (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Array α) :
    readArray read (array encode a) = .ok a := by
  change (a.map encode).mapM read = .ok a
  simp only [Array.mapM_map]
  have hf : (read ∘ encode) = (fun x => (pure x : Except String α)) :=
    funext h
  rw [hf]
  simpa [pure, Except.pure] using (Array.mapM_pure (m := Except String) (xs := a) (f := id))

theorem read_list (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : List α) :
    readList read (list encode a) = .ok a := by
  simp [readList, list, read_array encode read h, Functor.map, Except.map]

/-- Partial element decoders need only succeed on the supplied list. This
supports structurally bounded indices without assuming all indices are valid. -/
theorem read_list_of (encode : α → Json) (read : Json → Except String α)
    (a : List α) (h : ∀ x ∈ a, read (encode x) = .ok x) :
    readList read (list encode a) = .ok a := by
  change Array.toList <$> (a.toArray.map encode).mapM read = .ok a
  rw [Array.toList_mapM]
  simp only [Array.toList_map, List.mapM_map]
  induction a with
  | nil => simp [pure, Except.pure]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (fun y hy => h y (by simp [hy]))
    simp only [Function.comp_def] at hs
    simp [List.mapM_cons, Function.comp_def, hx, hs, bind, Except.bind,
      pure, Except.pure]

theorem read_vector (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Vector α n) :
    vector n read (array encode a.toArray) = .ok a := by
  have hm : (a.toArray.map encode).mapM read = .ok a.toArray := read_array encode read h _
  simp [vector, tuple, array, Json.getArr?, bind, Except.bind, pure, Except.pure,
    a.size_toArray, hm]

theorem read_option (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Option α) :
    readOption read (option encode a) = .ok a := by
  cases a <;> simp [readOption, option, Json.getArr?, bind, Except.bind, pure,
    Except.pure, h, Functor.map, Except.map]

theorem read_poly {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (h : value.Lawful) (p : DensePoly E) :
    readPoly value (poly value p) = .ok p := by
  simp [readPoly, poly, read_array value.encode value.decode h, bind, Except.bind,
    DensePoly.ofCoeffs_toArray, pure, Except.pure]

theorem read_endpoint {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (h : value.Lawful) (e : Endpoint E) :
    readEndpoint value (endpoint value e) = .ok e := by
  unfold ValueCodec.Lawful at h
  cases e <;> simp [readEndpoint, endpoint, Json.getArr?, bind, Except.bind, pure,
    Except.pure, h, Functor.map, Except.map]

/-- The standard JSON array instances use the same ordered traversal. -/
theorem read_jsonArray {α : Type} [ToJson α] [FromJson α]
    (h : ∀ x : α, fromJson? (toJson x) = .ok x) (a : Array α) :
    fromJson? (toJson a) = .ok a := read_array toJson fromJson? h a

theorem read_index (i : Fin n) : index n (toJson i.val) = .ok i := by
  simp [index, read_nat, bind, Except.bind, i.isLt, pure, Except.pure]

theorem read_matrix (a : Matrix Int n m) : matrix n m (encodeMatrix a) = .ok a := by
  have rows : (array (array toJson) (a.rows.toArray.map Vector.toArray)) =
      array (fun row : Vector Int m => array toJson row.toArray) a.rows.toArray := by
    simp [array, Array.map_map, Function.comp_def]
  rw [encodeMatrix, rows]
  have hv := read_vector (fun row : Vector Int m => array toJson row.toArray)
    (vector m fromJson?) (read_vector toJson fromJson? read_int) a.rows
  simp only [matrix, hv, Functor.map, Except.map]
  congr 1
  apply Matrix.ext
  exact Matrix.rows_ofRows _

end Codec
end Hex.SignDet
