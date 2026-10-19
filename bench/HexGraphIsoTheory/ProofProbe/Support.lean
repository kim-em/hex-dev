/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIsoTheory

/-! Recorded positive and negative random `n = 12` pairs as `SimpleGraph`s
for the Mathlib-route `graph_iso` CI examples. Cross-type goals remain covered
by `HexGraphIsoTheory/TacticTests.lean`. -/

namespace Hex.GraphIso.MathlibProofProbe

/-- Lexicographic pair index of `(i, j)`, `i < j`, over 12 vertices. -/
def pairIdx (i j : Nat) : Nat :=
  i * 12 - i * (i + 1) / 2 + (j - i - 1)

/-- The recorded pair bitmask of `Random.gnpMask ⟨Random.seed1⟩ 12`,
tied to the generator in the Mathlib-free probe support. -/
def mask12 : Nat := 48283412393242304007

/-- The recorded Fisher-Yates relabelling continuing the same stream. -/
def perm12 : Array Nat := #[11, 10, 1, 7, 3, 5, 4, 2, 9, 6, 8, 0]

/-- The recorded pair bitmask of `Random.gnpMask ⟨Random.seed2⟩ 12`. -/
def mask12b : Nat := 61032603037995048816

def gOfMask (mask : Nat) : SimpleGraph (Fin 12) where
  Adj i j := i ≠ j ∧
    mask.testBit (pairIdx (Nat.min i.val j.val) (Nat.max i.val j.val))
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa [Nat.min_comm, Nat.max_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance (mask : Nat) : DecidableRel (gOfMask mask).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

abbrev g12 : SimpleGraph (Fin 12) := gOfMask mask12

def g12relabelled : SimpleGraph (Fin 12) where
  Adj i j := i ≠ j ∧
    mask12.testBit (pairIdx
      (Nat.min perm12[i.val]! perm12[j.val]!)
      (Nat.max perm12[i.val]! perm12[j.val]!))
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by simpa [Nat.min_comm, Nat.max_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

instance : DecidableRel g12relabelled.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

abbrev g12b : SimpleGraph (Fin 12) := gOfMask mask12b

end Hex.GraphIso.MathlibProofProbe
