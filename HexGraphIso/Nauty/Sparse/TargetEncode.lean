/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetRank

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- Translate a cached cell start into the fresh selector's compact index,
retaining the singleton sentinel. -/
@[expose] def encode (keys : List Nat) (n k : Nat) : Nat :=
  if k = n then n else keys.idxOf k

theorem encode_lt {keys : List Nat} {n k : Nat} (hn : n ∉ keys)
    (hlen : keys.length ≤ n) (hk : k ∈ keys) : encode keys n k < n := by
  have he : k ≠ n := by intro he; subst k; exact hn hk
  simp only [encode, ite_eq_right he]
  have := List.idxOf_lt_length_of_mem hk
  omega

/-- The compact encoding is injective on all entries that a row can contain. -/
theorem encode_eq_iff {keys : List Nat} {n a b : Nat} (hn : n ∉ keys)
    (hlen : keys.length ≤ n) (ha : a ∈ keys) (hb : b = n ∨ b ∈ keys) :
    encode keys n b = encode keys n a ↔ b = a := by
  constructor
  · intro he
    rcases hb with hb | hb
    · subst b
      have hlt := encode_lt hn hlen ha
      simp only [encode, ite_true] at he
      have ha' : a ≠ n := by intro h; subst a; exact hn ha
      simp only [ite_eq_right ha'] at he
      simp only [encode, ite_eq_right ha'] at hlt
      omega
    · have ha' : a ≠ n := by intro h; subst a; exact hn ha
      have hb' : b ≠ n := by intro h; subst b; exact hn hb
      simp only [encode, ite_eq_right ha', ite_eq_right hb'] at he
      exact rank_inj hb ha he
  · intro h; rw [h]

/-- A row has the same number of incidences with a cell in either encoding. -/
theorem count_encode {keys row : List Nat} {n a : Nat} (hn : n ∉ keys)
    (hlen : keys.length ≤ n) (ha : a ∈ keys) (hr : ∀ v ∈ row, v = n ∨ v ∈ keys) :
    (row.map (encode keys n)).count (encode keys n a) = row.count a := by
  simp only [List.count_eq_countP, List.countP_map]
  apply List.countP_congr
  intro v hv
  simpa only [Function.comp_def, beq_iff_eq] using encode_eq_iff hn hlen ha (hr v hv)

theorem range_get (keys : List Nat) :
    (List.range keys.length).map (fun i => keys[i]!) = keys := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, getElem!_pos keys i hj]

/-- Compact-index join counts equal the counts over actual cell starts. -/
theorem scores_encode {keys row : List Nat} {n : Nat} {rankSize degree : Nat → Nat}
    (hn : keys.Nodup) (hsentinel : n ∉ keys) (hlen : keys.length ≤ n)
    (hr : ∀ v ∈ row, v = n ∨ v ∈ keys)
    (hs : ∀ i, i < keys.length → rankSize i = degree keys[i]!) :
    (List.range keys.length).countP (Join.qualifies (row.map (encode keys n)) rankSize) =
      keys.countP (Join.qualifies row degree) := by
  calc
    _ = (List.range keys.length).countP (fun i => Join.qualifies row degree keys[i]!) := by
      apply List.countP_congr
      intro i hi
      have hb := List.mem_range.mp hi
      have hm : keys[i]! ∈ keys := by rw [getElem!_pos _ i hb]; exact List.getElem_mem hb
      have he : keys[i]! ≠ n := by intro he; rw [he] at hm; exact hsentinel hm
      have henc : encode keys n keys[i]! = i := by rw [encode, ite_eq_right he, rank_get hn hb]
      have hc := count_encode hsentinel hlen hm hr
      rw [henc] at hc
      simp only [Join.qualifies, hc, hs i hb]
    _ = _ := by
      change (List.range keys.length).countP ((Join.qualifies row degree) ∘ (fun i => keys[i]!)) = _
      rw [← List.countP_map, range_get]

end Hex.GraphIso.Nauty.Sparse.Target
