/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.NativeCounts
public import HexGraphIso.Nauty.Sparse.RefineState

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt.Valid

variable {level : Nat} {s : RefineSt n}

/-- The complete singleton pass stabilizes its captured splitter in the
shared equitability predicate, using native row counts. -/
theorem singleton_const (h : Valid level s) (G : Hex.SparseGraph n) (split : Nat)
    (hb : split < n) :
    let t := splitSingleton (.ofGraph G) level split s
    ∀ a len, IsCell t.ptn level a len → a + len ≤ n →
      ConstOn (Graph.context G) (worksetOf n s.lab split split) (segN t.lab a len) := by
  have ht := splitSingleton_state G level split s h.lab h.size h.closed hb h.index
    ⟨h.scratch.marks_size, h.scratch.marks_le⟩ ⟨h.scratch.vmarks_size, h.scratch.vmarks_le⟩
  have hc := ht.2.2.2.2.2.2.1.done
  dsimp only
  intro a len ha hab
  apply Graph.constOn_workset G s.lab _ h.lab ht.1 (Nat.le_refl _) hb hab
  intro q r hq hq' hr hr'
  simpa using hc a len ha hab q r hq hq' hr hr'

/-- The complete nontrivial pass stabilizes its captured splitter in the
shared equitability predicate, including untouched zero-count cells. -/
theorem nontrivial_const (h : Valid level s) (G : Hex.SparseGraph n) (split len : Nat)
    (hc : IsCell s.ptn level split len) (hb : split + len ≤ n) :
    let t := splitNontrivial (.ofGraph G) level split s
    ∀ a size, IsCell t.ptn level a size → a + size ≤ n →
      ConstOn (Graph.context G) (worksetOf n s.lab split s.cellend[split]!) (segN t.lab a size) := by
  have ht := splitNontrivial_state G level split len s h.lab h.size h.closed h.index hc hb
    ⟨h.scratch.marks_size, h.scratch.marks_le⟩ h.scratch.hits_size
  have hcell := h.index.ends_eq split len hc hb (by have := hc.1; omega)
  have hpos := hc.1
  have hconstant := ht.2.2.2.2.2.2.1.done
  dsimp only
  intro a size ha hab
  apply Graph.constOn_workset G s.lab _ h.lab ht.1
    (by have := hc.1; omega) (by omega) hab
  exact hconstant a size ha hab

end Hex.GraphIso.Nauty.Sparse.RefineSt.Valid
