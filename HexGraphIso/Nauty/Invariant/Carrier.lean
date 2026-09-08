/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Orbits

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A checked generator maps one labelling pointwise onto another. -/
@[expose] def LabelCarrier (ctx : Ctx n) (ref cur : Array Nat)
    (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ = true ∧
    ∀ i, i < n → γ[ref[i]!]! = cur[i]!

/-- A checked carrier whose witnessing generator stabilizes one ancestor
frame.  Direct generator unwinds need only this witness.  Requiring every
recorded generator to stabilize the frame is stronger, and it fails away
from the first-path loop that consumes an orbit closure. -/
@[expose] def CellCarrier (ctx : Ctx n) (ptn : Array Nat) (level : Nat)
    (base ref cur : Array Nat) (store : Array (Array Nat)) : Prop :=
  ∃ γ ∈ store, checkAutom ctx.g γ = true ∧
    (∀ i, i < n → γ[ref[i]!]! = cur[i]!) ∧
    CellStab ptn level base γ

theorem CellCarrier.toLabel {ctx : Ctx n} {ptn : Array Nat} {level : Nat}
    {base ref cur : Array Nat} {store : Array (Array Nat)}
    (h : CellCarrier ctx ptn level base ref cur store) :
    LabelCarrier ctx ref cur store := by
  obtain ⟨γ, hmem, haut, hmap, _⟩ := h
  exact ⟨γ, hmem, haut, hmap⟩

/-- A checked carrier identifies the relabelled leaf rows of its two
permutation labellings. -/
theorem LabelCarrier.leafRows {ctx : Ctx n} {ref cur : Array Nat}
    {store : Array (Array Nat)}
    (h : LabelCarrier ctx ref cur store)
    (hgsz : ctx.g.size = n)
    (hrefsz : ref.size = n) (hrefok : LabOk ref n)
    (hcursz : cur.size = n) :
    leafRows ctx cur = leafRows ctx ref := by
  obtain ⟨γ, _, hcheck, hmap⟩ := h
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hgsz hcheck
  have hcur : cur = ref.map σ.toFun := by
    refine Array.ext (by rw [Array.size_map, hrefsz, hcursz])
      fun i hi hri => ?_
    rw [Array.getElem_map]
    have hrefi : i < ref.size := by omega
    have hm : γ[ref[i]]! = cur[i] := by
      simpa only [getElem!_pos ref i hrefi, getElem!_pos cur i hi] using
        hmap i (by omega)
    have hb : ref[i] < n := by
      simpa only [getElem!_pos ref i hrefi] using hrefok i (by omega)
    have hs := hσ ref[i] hb
    exact hm.symm.trans hs.symm
  rw [hcur]
  exact leafRows_map σ hrows hrefok hrefsz

end Hex.GraphIso.Nauty
