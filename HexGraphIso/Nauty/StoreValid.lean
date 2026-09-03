/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Translator

public section

/-!
Store validity for the admitted automorphisms (SPEC § Verified search
refinement, the replay hypothesis's store-validity clause).

The traced run's `genTrace` feeds the certificate producer: every
`.autom` record carries one of its entries, and the replay's
`validGammas` keeps only entries passing `checkAutom`, so a replayed
certificate needs every admitted entry to pass.

Both admission sites in `processnode` push the same shape of array: a
scatter `γ` with `γ[lab₁[i]!]! = lab₂[i]!` connecting two discrete
leaf labellings (code 1 scatters `lab` over `firstlab`, code 2
scatters `lab` over `canonlab`). This file proves the per-admission
facts about that shape: `scatter_isPerm` shows a scatter of one
permutation labelling over another is itself a permutation of
`[0, n)`, and `checkAutom_scatter_of_isautom` closes the code-1 arm
under its explicit `isautom` guard.

The code-1 arm's other guard, `gcaFirst ≥ noncheaplevel` with no
`isautom` scan, admits on the strength of `cheapautom`: an equitable
partition whose nontrivial cells are small enough forces every leaf
below to realize an automorphism. That argument needs a theory of
equitable partitions the development does not yet have; the theorems
here are stated so that arm can slot in beside them once proven.
-/

namespace Hex.GraphIso.Nauty

variable {nn : Nat}

/-- Entries of a permutation labelling are vertices. -/
private theorem perm_getElem!_lt {lab : Array Nat}
    (hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn))
    {i : Nat} (hi : i < nn) : lab[i]! < nn := by
  have hmem : lab[i]! ∈ lab.toList := by
    rw [getElem!_pos lab i (by omega)]
    exact List.getElem_mem (by simpa [hsz] using hi)
  exact List.mem_range.mp (hp.mem_iff.mp hmem)

/-- A permutation labelling attains every vertex. -/
private theorem perm_surj {lab : Array Nat}
    (hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn))
    {v : Nat} (hv : v < nn) : ∃ i, i < nn ∧ lab[i]! = v := by
  have hmem : v ∈ lab.toList := hp.mem_iff.mpr (List.mem_range.mpr hv)
  obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hmem
  refine ⟨i, by simpa [hsz] using hi, ?_⟩
  rw [getElem!_pos lab i (by simpa using hi)]
  simpa using hei

/-- A permutation labelling is injective on positions. -/
private theorem perm_inj {lab : Array Nat}
    (_hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn)) :
    ∀ a b, a < lab.size → b < lab.size → lab[a]! = lab[b]! → a = b := by
  intro a b ha hb hab
  have hnodup : lab.toList.Nodup := hp.symm.nodup List.nodup_range
  have hla : lab.toList[a]! = lab[a]! := by
    rw [getElem!_pos lab a ha, getElem!_pos _ a (by simpa using ha)]
    simp
  have hlb : lab.toList[b]! = lab[b]! := by
    rw [getElem!_pos lab b hb, getElem!_pos _ b (by simpa using hb)]
    simp
  exact (List.Nodup.getElem!_inj (by simpa using ha)
    (by simpa using hb) hnodup).mp (by rw [hla, hlb]; exact hab)

/-- The positions-to-entries map of a sized array, as a list. -/
private theorem map_range_getElem! {lab : Array Nat}
    (hsz : lab.size = nn) :
    ((List.range nn).map fun i => lab[i]!) = lab.toList := by
  refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos lab i (by simpa using h2)]
  simp

/-- The scatter of one permutation labelling over another is a
permutation of `[0, n)`: the `isPerm` side condition that
`checkAutom_of_isautom` consumes, produced from the two labellings'
permutation properties. -/
theorem scatter_isPerm {γ lab₁ lab₂ : Array Nat}
    (hsz₁ : lab₁.size = nn) (hp₁ : lab₁.toList.Perm (List.range nn))
    (hsz₂ : lab₂.size = nn) (hp₂ : lab₂.toList.Perm (List.range nn))
    (hsc : ∀ i, i < nn → γ[lab₁[i]!]! = lab₂[i]!) :
    (((List.range nn).map fun v => γ[v]!).isPerm (List.range nn)) =
      true := by
  rw [List.isPerm_iff]
  have h1 : ((List.range nn).map fun v => γ[v]!).Perm
      (lab₁.toList.map fun v => γ[v]!) := (hp₁.map _).symm
  have h2 : (lab₁.toList.map fun v => γ[v]!) =
      (List.range nn).map fun i => γ[lab₁[i]!]! := by
    rw [← map_range_getElem! hsz₁, List.map_map]
    rfl
  have h3 : ((List.range nn).map fun i => γ[lab₁[i]!]!) =
      (List.range nn).map fun i => lab₂[i]! :=
    List.map_congr_left fun i hi => hsc i (List.mem_range.mp hi)
  refine (h1.trans ?_)
  rw [h2, h3, map_range_getElem! hsz₂]
  exact hp₂

/-- The code-1 admission under its explicit `isautom` guard: the
scatter of the leaf labelling over the first-path labelling passes
`checkAutom` when the `isautom` scan accepted it. -/
theorem checkAutom_scatter_of_isautom {ctx : Ctx}
    {γ lab₁ lab₂ : Array Nat} (hγsz : γ.size = ctx.n)
    (hsz₁ : lab₁.size = ctx.n)
    (hp₁ : lab₁.toList.Perm (List.range ctx.n))
    (hsz₂ : lab₂.size = ctx.n)
    (hp₂ : lab₂.toList.Perm (List.range ctx.n))
    (hsc : ∀ i, i < ctx.n → γ[lab₁[i]!]! = lab₂[i]!)
    (hsymm : ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[i]!).testBit j = (ctx.g[j]!).testBit i)
    (hloop : ∀ i, i < ctx.n → (ctx.g[i]!).testBit i = false)
    (hb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (haut : isautom ctx γ = true) :
    checkAutom ctx.g γ ctx.n = true :=
  checkAutom_of_isautom hγsz (scatter_isPerm hsz₁ hp₁ hsz₂ hp₂ hsc)
    hsymm hloop hb haut

end Hex.GraphIso.Nauty
