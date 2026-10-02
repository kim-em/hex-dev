/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Rules

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std
attribute [local instance] lexOrd

namespace Replay

/-- Every enumerated leaf starts with the code of the actual refinement.
No well-formedness or nonemptiness premise is needed for this local rule. -/
theorem head_codes {G : Hex.SparseGraph n} {tcLevel fuel level numcells : Nat}
    {lab ptn : Array Nat} {active : VSet n} {l : SpecLeaf n}
    (h : l ∈ specLeaves G tcLevel (fuel + 1) level lab ptn active numcells) :
    ∃ cs, l.codes = (refine (.ofGraph G) level lab ptn active numcells).longcode :: cs := by
  rw [specLeaves] at h
  split at h
  · split at h
    · cases h
    · have he := List.mem_singleton.mp h
      rw [he]
      exact ⟨[codeSentinel], rfl⟩
  · obtain ⟨o, _, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hm
    exact ⟨q.codes, rfl⟩

theorem code_cmp {G H : Hex.SparseGraph n} {l : SpecLeaf n}
    {c b : Nat} {cs bs : List Nat} (hc : l.codes = c :: cs)
    (hlt : compare c b = .lt) : Key.cmp (l.key G) ⟨b :: bs, H⟩ = .lt := by
  simp only [Key.cmp, SpecLeaf.key, hc, List.compare_cons_cons, hlt, Ordering.then]

/-- A strictly smaller recomputed code covers the complete native subtree
and cannot hide an attaining leaf. -/
theorem prune_valid {G H : Hex.SparseGraph n} {tcLevel fuel level numcells b : Nat}
    {lab ptn : Array Nat} {active : VSet n} {bs : List Nat}
    (h : compare (refine (.ofGraph G) level lab ptn active numcells).longcode b = .lt) :
    Valid G ⟨b :: bs, H⟩
      (specLeaves G tcLevel (fuel + 1) level lab ptn active numcells) false := by
  have hcmp : ∀ l ∈ specLeaves G tcLevel (fuel + 1) level lab ptn active numcells,
      Key.cmp (l.key G) ⟨b :: bs, H⟩ = .lt := by
    intro l hl
    obtain ⟨cs, hc⟩ := head_codes hl
    exact code_cmp hc h
  constructor
  · intro l hl
    exact Ordering.isLE_of_eq_lt (hcmp l hl)
  · constructor
    · intro hf
      cases hf
    · rintro ⟨l, hl, he⟩
      have hc := Key.cmp_eq.mpr he
      rw [hcmp l hl] at hc
      contradiction

/-- A bound on a nonempty subtree bounds its leading refinement code. -/
theorem code_le {G H : Hex.SparseGraph n} {l : SpecLeaf n}
    {c b : Nat} {cs bs : List Nat} (hc : l.codes = c :: cs)
    (h : Key.Le (l.key G) ⟨b :: bs, H⟩) : c ≤ b := by
  by_cases hn : c ≤ b
  · exact hn
  have hgt : compare c b = .gt := Nat.compare_eq_gt.mpr (by omega)
  simp only [Key.Le, Key.cmp, SpecLeaf.key, hc, List.compare_cons_cons,
    hgt, Ordering.then, Ordering.isLE] at h
  contradiction

end Replay
end Hex.GraphIso.Nauty.Sparse
