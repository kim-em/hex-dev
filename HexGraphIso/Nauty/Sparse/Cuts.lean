/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Invariant.Refine

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A sequence of increasing partition cuts charges the cell counter exactly
once per new boundary, leaving the unprocessed suffix untouched. -/
structure Cuts (level n : Nat) (before ptn : Array Nat) (old count upto : Nat) : Prop where
  size : ptn.size = before.size
  count : bcount ptn level n + old = bcount before level n + count
  tail : ∀ q : Nat, upto ≤ q → ptn[q]! = before[q]!
  closed : ∀ q : Nat, before[q]! ≤ level → ptn[q]! = before[q]!

namespace Cuts

variable {level n old count upto next q : Nat} {before ptn : Array Nat}

theorem refl (level n : Nat) (ptn : Array Nat) (count upto : Nat) :
    Cuts level n ptn ptn count count upto := ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem move (h : Cuts level n before ptn old count upto) (hu : upto ≤ next) :
    Cuts level n before ptn old count next :=
  ⟨h.size, h.count, fun q hq => h.tail q (by omega), h.closed⟩

theorem cut (h : Cuts level n before ptn old count upto)
    (hq : upto ≤ q) (hn : q < n) (hs : q < before.size) (ho : level < before[q]!) :
    Cuts level n before (ptn.setIfInBounds q level) old (count + 1) (q + 1) := by
  have hb : q < ptn.size := by rw [h.size]; exact hs
  have hop : level < ptn[q]! := by rw [h.tail q hq]; exact ho
  refine ⟨by simpa using h.size, ?_, ?_, ?_⟩
  · change bcount (ptn.set! q level) level n + old = _
    rw [bcount_set!_open hb hop hn]
    have := h.count
    omega
  · intro r hr
    change (ptn.set! q level)[r]! = _
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    exact h.tail r (by omega)
  · intro r hr
    change (ptn.set! q level)[r]! = _
    rw [Array.getElem!_set!_ne _ _ _ _ (by intro he; subst r; omega)]
    exact h.closed r hr

theorem initial (ptn : Array Nat) (count : Nat)
    (hq : q < upto) (hn : q < n) (hs : q < ptn.size) (ho : level < ptn[q]!) :
    Cuts level n ptn (ptn.setIfInBounds q level) count (count + 1) upto :=
  ((refl level n ptn count q).cut (Nat.le_refl _) hn hs ho).move (by omega)

theorem initial_count (ptn : Array Nat) (count : Nat)
    (hn : q < n) (hs : q < ptn.size) (ho : level < ptn[q]!) :
    bcount (ptn.setIfInBounds q level) level n + count =
      bcount ptn level n + (count + 1) :=
  (initial ptn count (by omega : q < q + 1) hn hs ho).count

/-- Successive passes compose their exact counter changes and retain every
inherited closed value. -/
theorem trans {middle : Array Nat} {middleCount : Nat}
    (h : Cuts level n before middle old middleCount upto)
    (h' : Cuts level n middle ptn middleCount count upto) :
    Cuts level n before ptn old count upto := by
  refine ⟨h'.size.trans h.size, ?_, ?_, ?_⟩
  · have := h.count
    have := h'.count
    omega
  · intro q hq
    rw [h'.tail q hq, h.tail q hq]
  · intro q hq
    have he := h.closed q hq
    rw [h'.closed q (by omega), he]

/-- Closing one open position extends an already completed pass. -/
theorem insert (h : Cuts level n before ptn old count n)
    (hn : q < n) (hs : q < ptn.size) (ho : level < ptn[q]!) :
    Cuts level n before (ptn.setIfInBounds q level) old (count + 1) n :=
  h.trans (initial ptn count hn hn hs ho)

end Cuts
end Hex.GraphIso.Nauty.Sparse
