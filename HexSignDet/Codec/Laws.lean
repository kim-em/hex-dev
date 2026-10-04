/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Codec.Basic
import all HexSignDet.Codec.Basic
import all HexSignDet.Codec.Json

public section

namespace Hex.SignDet
open Codec (Json)

/-- Structured encoding followed by decoding preserves the entire input value.
This law does not include JSON printing or byte parsing. It is needed for
structured and byte roundtrips, not for soundness of independent replay. -/
@[expose] def ValueCodec.Lawful (codec : ValueCodec α) : Prop :=
  ∀ x, codec.decode (codec.encode x) = .ok x

namespace Codec

@[simp] theorem read_nat (n : Nat) : Json.decode (Json.of n) = .ok n := by
  rfl

@[simp] theorem read_int (n : Int) : Json.decode (Json.of n) = .ok n := by
  rfl

end Codec

theorem ValueCodec.nat_lawful : nat.Lawful := Codec.read_nat

theorem ValueCodec.rat_lawful : rat.Lawful := by
  intro q
  simp [rat, Json.getArr_arr, bind, Except.bind, pure, Except.pure, q.den_nz, Rat.mkRat_self]

/-- Successful strict reads preserve the exact result of another decoder. -/
@[expose] def ValueCodec.Refines (strict complete : ValueCodec α) : Prop :=
  ∀ j a, strict.decode j = .ok a → complete.decode j = .ok a

namespace Codec

private theorem list_refines (strict complete : α → Except String β)
    (h : ∀ x y, strict x = .ok y → complete x = .ok y)
    (xs : List α) (ys : List β) (hs : xs.mapM strict = .ok ys) :
    xs.mapM complete = .ok ys := by
  induction xs generalizing ys with
  | nil => simpa using hs
  | cons x xs ih =>
    simp only [List.mapM_cons] at hs ⊢
    cases hx : strict x with
    | error e => simp [hx, bind, Except.bind] at hs
    | ok y =>
      simp only [hx, bind, Except.bind] at hs
      cases ht : xs.mapM strict with
      | error e => simp [ht] at hs
      | ok tail =>
        simp only [ht, pure, Except.pure, Except.ok.injEq] at hs
        subst ys
        simp [h x y hx, ih tail ht, bind, Except.bind, pure, Except.pure]

/-- Refinement lifts through the actual ordered array reader. -/
theorem readArray_refines (strict complete : Json → Except String α)
    (h : ∀ j a, strict j = .ok a → complete j = .ok a)
    (j : Json) (a : Array α) (ha : readArray strict j = .ok a) :
    readArray complete j = .ok a := by
  unfold readArray at ha ⊢
  cases hj : j.getArr? with
  | error e => simp [hj, bind, Except.bind] at ha
  | ok raw =>
    simp only [hj, bind, Except.bind] at ha ⊢
    have hl : raw.toList.mapM strict = .ok a.toList := by
      rw [← Array.toList_mapM]
      simp [ha, Functor.map, Except.map]
    have hg := list_refines strict complete h raw.toList a.toList hl
    rw [← Array.toList_mapM] at hg
    cases hr : raw.mapM complete with
    | error e => simp [hr, Functor.map, Except.map] at hg
    | ok b =>
      simp only [hr, Functor.map, Except.map, Except.ok.injEq, Array.toList_inj] at hg
      cases hg
      rfl

/-- Polynomial decoding preserves every literal coefficient under refinement. -/
theorem readPoly_refines {E : Type} (strict complete : ValueCodec E) [Zero E] [DecidableEq E]
    (h : strict.Refines complete) (j : Json) (p : DensePoly E)
    (hp : readPoly strict j = .ok p) : readPoly complete j = .ok p := by
  unfold readPoly at hp ⊢
  cases hr : readArray strict.decode j with
  | error e => simp [hr, bind, Except.bind] at hp
  | ok a =>
    have hc := readArray_refines strict.decode complete.decode h j a hr
    simp only [hr, hc, bind, Except.bind] at hp ⊢
    exact hp

/-- Element roundtrips lift through the actual ordered array decoder. -/
theorem read_array (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Array α) :
    readArray read (array encode a) = .ok a := by
  unfold readArray array
  rw [Json.getArr_arr]
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
  unfold readList list readArray array
  rw [Json.getArr_arr]
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

/-- Partial decoders need only cover the actual array entries. -/
theorem read_array_of (encode : α → Json) (read : Json → Except String α)
    (a : Array α) (h : ∀ x ∈ a, read (encode x) = .ok x) :
    readArray read (array encode a) = .ok a := by
  have hl := read_list_of encode read a.toList (fun x hx => h x (by simpa using hx))
  simp only [readList, list, Array.toArray_toList] at hl
  cases hr : readArray read (array encode a) with
  | error e => simp [hr, Functor.map, Except.map] at hl
  | ok b =>
    simp only [hr, Functor.map, Except.map, Except.ok.injEq, Array.toList_inj] at hl
    cases hl
    rfl

theorem read_vector (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Vector α n) :
    vector n read (array encode a.toArray) = .ok a := by
  have hm : (a.toArray.map encode).mapM read = .ok a.toArray := by
    simpa [readArray, array, bind, Except.bind] using read_array encode read h a.toArray
  simp [vector, tuple, array, Json.getArr_arr, bind, Except.bind, pure, Except.pure,
    a.size_toArray, hm]

theorem read_option (encode : α → Json) (read : Json → Except String α)
    (h : ∀ x, read (encode x) = .ok x) (a : Option α) :
    readOption read (option encode a) = .ok a := by
  cases a <;> simp [readOption, option, Json.getArr_arr, bind, Except.bind, pure,
    Except.pure, h, Functor.map, Except.map]

theorem read_poly {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (h : value.Lawful) (p : DensePoly E) :
    readPoly value (poly value p) = .ok p := by
  simp [readPoly, poly, read_array value.encode value.decode h, bind, Except.bind,
    DensePoly.ofCoeffs_toArray, pure, Except.pure]

/-- A polynomial roundtrip needs only the coefficients it actually stores. -/
theorem read_poly_of {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (p : DensePoly E)
    (h : ∀ x ∈ p.toArray, value.decode (value.encode x) = .ok x) :
    readPoly value (poly value p) = .ok p := by
  simp [readPoly, poly, read_array_of value.encode value.decode p.toArray h,
    bind, Except.bind, DensePoly.ofCoeffs_toArray, pure, Except.pure]

theorem read_endpoint {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (h : value.Lawful) (e : Endpoint E) :
    readEndpoint value (endpoint value e) = .ok e := by
  unfold ValueCodec.Lawful at h
  cases e <;> simp [readEndpoint, endpoint, Json.getArr_arr, bind, Except.bind, pure,
    Except.pure, h, Functor.map, Except.map]

/-- An endpoint roundtrip needs only its actual finite coefficient. -/
theorem read_endpoint_of {E : Type} (value : ValueCodec E) (endpoint : Endpoint E)
    (covered : ∀ x, endpoint = .finite x → value.decode (value.encode x) = .ok x) :
    Codec.readEndpoint value (Codec.endpoint value endpoint) = .ok endpoint := by
  cases endpoint with
  | negInf => rfl
  | posInf => rfl
  | finite x =>
    simp [Codec.readEndpoint, Codec.endpoint, Codec.Json.getArr_arr, covered x rfl,
      bind, Except.bind, Functor.map, Except.map]

/-- The standard JSON array instances use the same ordered traversal. -/
theorem read_jsonArray {α : Type} [Json.To α] [Json.From α]
    (h : ∀ x : α, Json.decode (Json.of x) = .ok x) (a : Array α) :
    Json.decode (Json.of a) = .ok a := read_array Json.of Json.decode h a

theorem read_index (i : Fin n) : index n (Json.of i.val) = .ok i := by
  simp [index, bind, Except.bind, i.isLt, pure, Except.pure]

theorem read_matrix (a : Matrix Int n m) : matrix n m (encodeMatrix a) = .ok a := by
  have rows : (array (array Json.of) (a.rows.toArray.map Vector.toArray)) =
      array (fun row : Vector Int m => array Json.of row.toArray) a.rows.toArray := by
    simp [array, Array.map_map, Function.comp_def]
  rw [encodeMatrix, rows]
  have hv := read_vector (fun row : Vector Int m => array Json.of row.toArray)
    (vector m Json.decode) (read_vector Json.of Json.decode read_int) a.rows
  simp only [matrix, hv, Functor.map, Except.map]
  congr 1
  apply Matrix.ext
  exact Matrix.rows_ofRows _

end Codec
end Hex.SignDet
