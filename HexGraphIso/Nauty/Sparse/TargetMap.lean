/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetEncode

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The compact-index map is installed through `upto`; untouched vertices
retain the singleton sentinel from the initial allocation. -/
structure MapPrefix (n : Nat) (lab cache : Array Nat) (keys : List Nat) (upto : Nat)
    (raw : Array Nat) : Prop where
  size : raw.size = n
  get : ∀ i, i < n → raw[lab[i]!]! = if i < upto then encode keys n cache[lab[i]!]! else n

namespace MapPrefix

theorem initial {n : Nat} {lab cache : Array Nat} (keys : List Nat)
    (hb : ∀ i, i < n → lab[i]! < n) :
    MapPrefix n lab cache keys 0 (Array.replicate n n) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  simp [hb i hi]

/-- Installing one nontrivial cell extends the map without changing earlier
vertices; the source performs exactly this scatter with its compact index. -/
theorem advance {n first last value : Nat} {lab cache raw out : Array Nat} {keys : List Nat}
    (h : MapPrefix n lab cache keys first raw)
    (hscatter : Index.Scatter n lab raw out first (last + 1) value)
    (horder : first ≤ last) (hv : ∀ i, first ≤ i → i ≤ last →
      encode keys n cache[lab[i]!]! = value) :
    MapPrefix n lab cache keys (last + 1) out := by
  refine ⟨hscatter.size, ?_⟩
  intro i hi
  rw [hscatter.get i hi, h.get i hi]
  by_cases hb : i < first
  · simp only [ite_eq_right (show ¬(first ≤ i ∧ i < last + 1) by omega),
      ite_eq_left hb, ite_eq_left (show i < last + 1 by omega)]
  · by_cases he : i ≤ last
    · rw [ite_eq_left (by omega), ite_eq_left (by omega), hv i (by omega) he]
    · rw [ite_eq_right (by omega), ite_eq_right hb, ite_eq_right (by omega)]

/-- One executed scatter assignment extends the installed positional prefix. -/
theorem set {n i value : Nat} {lab cache raw : Array Nat} {keys : List Nat}
    (h : MapPrefix n lab cache keys i raw) (hi : i < n)
    (hbound : ∀ j, j < n → lab[j]! < n)
    (hinj : ∀ a b, a < n → b < n → lab[a]! = lab[b]! → a = b)
    (hv : value = encode keys n cache[lab[i]!]!) :
    MapPrefix n lab cache keys (i + 1) (raw.set! lab[i]! value) := by
  refine ⟨by simpa using h.size, ?_⟩
  intro j hj
  by_cases he : j = i
  · subst j
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hbound i hi),
      ite_eq_left (by omega), hv]
  · rw [Array.getElem!_set!_ne _ _ _ _ (fun hh => he (hinj j i hj hi hh.symm)), h.get j hj]
    have hh : (j < i + 1) ↔ j < i := by omega
    simp only [hh]

/-- A singleton needs no write: its unchanged sentinel is already correct. -/
theorem singleton {n first : Nat} {lab cache raw : Array Nat} {keys : List Nat}
    (h : MapPrefix n lab cache keys first raw) (hc : cache[lab[first]!]! = n) :
    MapPrefix n lab cache keys (first + 1) raw := by
  refine ⟨h.size, ?_⟩
  intro i hi
  rw [h.get i hi]
  by_cases he : i = first
  · subst i
    simp [hc, encode]
  · have heq : (i < first + 1) ↔ i < first := by omega
    simp only [heq]

/-- A cursor beyond the vertex range has installed every position. -/
theorem finish {n upto : Nat} {lab cache raw : Array Nat} {keys : List Nat}
    (h : MapPrefix n lab cache keys upto raw) (hu : n ≤ upto) :
    MapPrefix n lab cache keys n raw := by
  refine ⟨h.size, ?_⟩
  intro i hi
  rw [h.get i hi, ite_eq_left (by omega), ite_eq_left hi]

/-- The completed scatter agrees with the compact encoding on every vertex,
using the checked label's inverse to recover its unique position. -/
theorem complete {n : Nat} {lab cache raw : Array Nat} {keys : List Nat}
    (h : MapPrefix n lab cache keys n raw) (l : Label n)
    (hl : Label.ofArray? n lab = some l) (v : Fin n) :
    raw[v.val]! = encode keys n cache[v.val]! := by
  have hv : lab[(l.toPerm.get v).val]! = v.val := by
    rw [← Label.ofArray?_get hl _ (l.toPerm.get v).isLt, Label.get_toPerm_get]
  have he := h.get _ (l.toPerm.get v).isLt
  simpa only [ite_eq_left (l.toPerm.get v).isLt, hv] using he

end MapPrefix

end Hex.GraphIso.Nauty.Sparse.Target
