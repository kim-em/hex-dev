/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstRef
public import HexGraphIso.Nauty.Policy.FirstEntry
public import HexGraphIso.Nauty.Generation.Matching
import all HexGraphIso.Nauty.Policy.FirstRef
import all HexGraphIso.Nauty.Policy.FirstEntry
import all HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.Orbits
import all HexGraphIso.Nauty.Policy.MaxBoundary
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Generation.Reference
import all HexGraphIso.Nauty.Generation.Coverage
import all HexGraphIso.Nauty.Generation.Matching

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- The selected descent uses the same target rule as a reference occurrence. -/
theorem Selects.reference {ctx : Ctx n} {tcLevel level : Nat}
    {root : RefineSt n} {path : List (Nat × Nat)}
    (h : Selects ctx tcLevel level root path) :
    Generation.referenceTargets ctx tcLevel level root path := by
  induction path generalizing level root with
  | nil => trivial
  | cons step path ih =>
    cases step
    exact ⟨h.1.symm, ih h.2⟩

/-- The two path-code definitions enumerate the same refined nodes. -/
theorem pathCodes_reference (ctx : Ctx n) (level : Nat) (root : RefineSt n)
    (path : List (Nat × Nat)) :
    pathCodes ctx level root path = Generation.referenceCodes ctx level root path := by
  induction path generalizing level root with
  | nil => rfl
  | cons step path ih =>
    cases step
    simp only [pathCodes, Generation.referenceCodes, ih]

/-- A saved first descent supplies occurrence and exact stored matching,
including the terminal sentinel. Neither conclusion assumes key maximality. -/
theorem FirstRef.occurs {ctx : Ctx n} {tcLevel level : Nat}
    {root : RefineSt n} {st : Search n} (h : FirstRef ctx tcLevel level root st) :
    ∃ targets key, Generation.HasLeaf ctx tcLevel level root targets key ∧
      Generation.Matches ctx level st targets key := by
  let codes := pathCodes ctx level root h.path
  refine ⟨h.path.map Prod.fst, ⟨codes ++ [codeSentinel], leafRows ctx st.firstlab⟩,
    ⟨h.path, h.last, h.leaf, h.descent, Selects.reference h.selects, h.discrete, rfl, ?_⟩, ?_⟩
  · rw [h.lab, ← pathCodes_reference]
  · constructor
    · intro i hi
      change (codes ++ [codeSentinel])[i]! = st.firstcode[level + i]!
      by_cases hlt : i < codes.length
      · rw [getElem!_append_left hlt]
        exact (h.codes i hlt).symm
      · have hieq : i = codes.length := by
          change i < (codes ++ [codeSentinel]).length at hi
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst i
        have hlength : level + codes.length = h.last + 1 := by
          dsimp only [codes]
          rw [pathCodes_length]
          have hd := h.descent.length
          omega
        rw [hlength, h.sentinel]
        simp
    · intro i hi
      exact (h.targets i hi).symm
    · rfl

/-- A valid first call produces a matching occurrence from its actual
descent, without assuming the call's maximum or its return level. -/
theorem FirstPre.occurs {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel fuel level numcells : Nat} {st : Search n}
    (h : FirstPre G ctx level numcells st)
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hempty : st.genTrace = #[]) (hfuel : n + 1 ≤ level + fuel) :
    ∃ targets key,
      Generation.HasLeaf ctx tcLevel level (st.refined ctx level numcells) targets key ∧
      Generation.Matches ctx level (node true ctx inf tcLevel fuel level numcells st).2
        targets key := by
  obtain ⟨last, leaf, hp⟩ := firstPath_exists (ctx := ctx) (tcLevel := tcLevel)
    hn0 h.positive h.partition (Max.empty_orbits h.orbits hempty) hfuel
  obtain ⟨href, _⟩ := firstRef_of_path (inf := inf) hn0 hsymm hp h.positive h.partition
    h.equitable h.targets h.codes
  exact href.occurs

end Hex.GraphIso.Nauty
