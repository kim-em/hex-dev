/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Trace
public import HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A permutation stabilizes the ordered colour cells of the initial partition. -/
def ColorStab (G : Colored n k) (perm : Array Nat) : Prop :=
  CellStab (initPtn n (n + 2) (initialPartition G).2) 1 (initialPartition G).1 perm

/-- Every recorded generator stabilizes the initial colour partition. -/
def TraceStab (G : Colored n k) (st : Search n) : Prop :=
  ∀ perm ∈ st.genTrace, ColorStab G perm

/-- Retaining the trace retains its colour stabilization. -/
theorem TraceStab.congr {G : Colored n k} {st out : Search n}
    (h : TraceStab G st) (ht : out.genTrace = st.genTrace) : TraceStab G out := by
  intro perm hp
  rw [ht] at hp
  exact h perm hp

/-- Scattering two reached labellings preserves the initial colour cells. -/
theorem scatter_color {G : Colored n k} {ref : Array Nat} {st : Search n}
    (hn0 : 0 < n) (href : ref.size = n) (hperm : ref.toList.Perm (List.range n))
    (hr : CellsReach G ref) (hl : CellsReach G st.lab) (hw : st.workperm.size = n) :
    ColorStab G (scatter ref st).workperm := by
  have hroot := initial_nodeOk G hn0
  exact cellStab_of_scatter hroot.ptnSize hroot.labSize href hroot.ptnEnd
    hr hl (scatter_map hw href hperm)

private theorem canonVerdict_stab {G : Colored n k} {ctx : Ctx n}
    {level : Nat} {st out : Search n}
    (hauto : canonVerdict ctx level st = (.autoCanon, out))
    (hn0 : 0 < n) (hw : st.workperm.size = n)
    (href : st.canonlab.size = n) (hr : CellsReach G st.canonlab) (hl : CellsReach G st.lab) :
    ColorStab G out.workperm := by
  by_cases hcomp : st.compCanon = 0
  · by_cases hlevel : level < st.canonlevel
    · simp [canonVerdict, hcomp, hlevel] at hauto
    · simp only [canonVerdict, hcomp, beq_self_eq_true, ite_true, hlevel, ite_false] at hauto
      split at hauto
      · have hs := scatter_color hn0 href (isPerm_of_cellsReach href hn0 hr) hr hl hw
        have hout := (Prod.mk.inj hauto).2
        rw [← hout]
        rw [scatter_eq] at hs ⊢
        exact hs
      · split at hauto <;> cases hauto
  · simp only [canonVerdict, beq_eq_false_iff_ne.mpr hcomp, Bool.false_eq_true, ite_false] at hauto
    split at hauto <;> cases hauto

/-- Canonical admissions preserve colours even if a failed first scan filled the scratch array. -/
theorem classify_canon_stab {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st out : Search n} (hauto : classify ctx level numcells st = (.autoCanon, out))
    (hn0 : 0 < n) (hw : st.workperm.size = n)
    (href : st.canonlab.size = n) (hr : CellsReach G st.canonlab) (hl : CellsReach G st.lab) :
    ColorStab G out.workperm := by
  rw [classify_eq] at hauto
  split at hauto
  · cases hauto
  · split at hauto
    · cases hauto
    · split at hauto
      · dsimp only at hauto
        split at hauto
        · cases hauto
        · apply canonVerdict_stab hauto hn0 ((scatter_size st.firstlab st).trans hw)
          all_goals simpa only [scatter_eq] using (by assumption)
      · exact canonVerdict_stab hauto hn0 hw href hr hl

/-- Both automorphism classifications fill the scratch array with a colour-stabilizing scatter. -/
theorem classify_stab {G : Colored n k} {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hw : st.workperm.size = n)
    (hf : st.firstlab.size = n) (hfr : CellsReach G st.firstlab)
    (hc : st.canonlab.size = n) (hcr : CellsReach G st.canonlab) (hl : CellsReach G st.lab) :
    let result := classify ctx level numcells st
    result.1 = .autoFirst ∨ result.1 = .autoCanon → ColorStab G result.2.workperm := by
  intro result ha
  rcases ha with ha | ha
  · have hv : classify ctx level numcells st = (.autoFirst, result.2) := Prod.ext ha rfl
    obtain ⟨_, _, hout, _⟩ := classify_first hv
    rw [hout]
    exact scatter_color hn0 hf (isPerm_of_cellsReach hf hn0 hfr) hfr hl hw
  · exact classify_canon_stab (Prod.ext ha rfl) hn0 hw hc hcr hl

/-- Leaf actions preserve colour stabilization when both admission cases supply it. -/
theorem TraceStab.leaf {G : Colored n k} {st : Search n} (h : TraceStab G st)
    (leaf : Leaf) (level : Nat)
    (hc : leaf = .autoFirst ∨ leaf = .autoCanon → ColorStab G st.workperm) :
    TraceStab G (leafExit leaf level st).2 := by
  intro perm hp
  cases leaf with
  | autoFirst =>
    rw [leafExit_trace, Array.mem_push] at hp
    exact hp.elim (h perm) (fun he => he ▸ hc (Or.inl rfl))
  | autoCanon =>
    rw [leafExit_trace, Array.mem_push] at hp
    exact hp.elim (h perm) (fun he => he ▸ hc (Or.inr rfl))
  | internal => exact h perm hp
  | better sr => rw [leafExit_trace] at hp; exact h perm hp
  | bad => rw [leafExit_trace] at hp; exact h perm hp

end Hex.GraphIso.Nauty.Engine
