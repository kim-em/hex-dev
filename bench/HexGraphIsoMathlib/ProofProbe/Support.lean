/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGraphIsoMathlib
import Mathlib.Data.Fintype.Powerset

/-!
Shared inputs for the Mathlib-route `graph_iso` fresh-module probes
(SPEC/hex-graph-iso-mathlib § Tests): the generalized Petersen and
Kneser graphs of the manual chapter on their genuinely different
vertex types, and the recorded random `n = 12` pair as `SimpleGraph`s
over `Fin 12`. Each probe case imports this module and nothing else
beyond it, measured against `MathlibBaseline`'s matched import cost.
-/

namespace Hex.GraphIso.MathlibProofProbe

def gpetersen (p q : Nat) :
    SimpleGraph (Fin 2 × Fin p) where
  Adj v w :=
    v ≠ w ∧
      ((v.1 = 0 ∧ w.1 = 0 ∧
          (w.2.val = (v.2.val + 1) % p ∨
            v.2.val = (w.2.val + 1) % p)) ∨
       (v.1 = 1 ∧ w.1 = 1 ∧
          (w.2.val = (v.2.val + q) % p ∨
            v.2.val = (w.2.val + q) % p)) ∨
       (v.1 ≠ w.1 ∧ v.2 = w.2))
  symm := ⟨by
    intro v w h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b⟩
    · exact Or.inl ⟨b, a, c.symm⟩
    · exact Or.inr (Or.inl ⟨b, a, c.symm⟩)
    · exact Or.inr (Or.inr ⟨fun e => a e.symm, b.symm⟩)⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

instance (p q : Nat) : DecidableRel (gpetersen p q).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

def kneser (m r : Nat) :
    SimpleGraph {s : Finset (Fin m) // s.card = r} where
  Adj s t := Disjoint s.val t.val ∧ s ≠ t
  symm := ⟨by intro s t h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro s h; exact h.2 rfl⟩

instance (m r : Nat) : DecidableRel (kneser m r).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

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
