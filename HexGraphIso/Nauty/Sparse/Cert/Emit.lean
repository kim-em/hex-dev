/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Cert.Siblings

public section

namespace Hex.GraphIso.Nauty.Sparse.Replay

/-- An accepted ordinary node enters the sibling scan with the same flag. -/
theorem sibling_of_check {check : Nat → CertNode → Option Bool}
    {witness : Nat → Nat → Array Nat → Bool} {seen : Array Bool} {o : Nat}
    {c : CertNode} {a : Bool}
    (hne : ∀ earlier raw, c ≠ .autom earlier raw) (hs : seen.size = o)
    (h : check o c = some a) : sibling check witness seen c = some a := by
  cases c with
  | autom earlier raw => exact False.elim (hne earlier raw rfl)
  | leaf => simpa only [sibling, hs] using h
  | codePrune => simpa only [sibling, hs] using h
  | node cs => simpa only [sibling, hs] using h

/-- Emit a checked earlier-sibling reference when available. The fallback
is a function so compiled execution never expands a pruned subtree eagerly. -/
@[expose] def emit (choose : Nat → Option (Nat × Array Nat))
    (witness : Nat → Nat → Array Nat → Bool) (fallback : Nat → CertNode) (o : Nat) : CertNode :=
  match choose o with
  | some (earlier, images) =>
    if earlier < o ∧ witness o earlier images = true then .autom earlier images
    else fallback o
  | none => fallback o

/-- Emission cannot invalidate a successful fallback: a reference is emitted
only after exactly the same check that the sibling scan will replay. -/
theorem emit_replays {choose : Nat → Option (Nat × Array Nat)}
    {witness : Nat → Nat → Array Nat → Bool} {fallback : Nat → CertNode}
    {check : Nat → CertNode → Option Bool} {seen : Array Bool} {o : Nat}
    (hs : seen.size = o)
    (h : ∃ a, sibling check witness seen (fallback o) = some a) :
    ∃ a, sibling check witness seen (emit choose witness fallback o) = some a := by
  rw [emit]
  split
  · rename_i earlier images he
    split
    · rename_i hw
      exact ⟨seen[earlier]!, by simp only [sibling, hs, hw.1, hw.2, and_self, ite_true]⟩
    · exact h
  · exact h

end Hex.GraphIso.Nauty.Sparse.Replay
