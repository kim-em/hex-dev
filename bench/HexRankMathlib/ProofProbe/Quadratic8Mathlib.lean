/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormRank
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

set_option maxHeartbeats 0

theorem result : Matrix.rank (R := GaussianInt) !![⟨1, 1⟩, ⟨-9, -9⟩, ⟨-3, -3⟩, ⟨0, 0⟩, ⟨-8, -8⟩, ⟨-3, -3⟩, ⟨4, 4⟩, ⟨7, 7⟩;
  ⟨9, 18⟩, ⟨-7, -14⟩, ⟨0, 0⟩, ⟨-7, -14⟩, ⟨8, 16⟩, ⟨-5, -10⟩, ⟨3, 6⟩, ⟨-9, -18⟩;
  ⟨-6, -18⟩, ⟨1, 3⟩, ⟨-2, -6⟩, ⟨1, 3⟩, ⟨-6, -18⟩, ⟨-1, -3⟩, ⟨0, 0⟩, ⟨-1, -3⟩;
  ⟨-8, -8⟩, ⟨-4, -4⟩, ⟨8, 8⟩, ⟨-6, -6⟩, ⟨-6, -6⟩, ⟨5, 5⟩, ⟨5, 5⟩, ⟨-4, -4⟩;
  ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-4, -8⟩, ⟨-9, -18⟩, ⟨2, 4⟩, ⟨-6, -12⟩, ⟨0, 0⟩, ⟨8, 16⟩;
  ⟨1, 3⟩, ⟨6, 18⟩, ⟨-6, -18⟩, ⟨2, 6⟩, ⟨2, 6⟩, ⟨1, 3⟩, ⟨2, 6⟩, ⟨8, 24⟩;
  ⟨-8, -8⟩, ⟨5, 5⟩, ⟨-8, -8⟩, ⟨3, 3⟩, ⟨8, 8⟩, ⟨2, 2⟩, ⟨8, 8⟩, ⟨-8, -8⟩;
  ⟨-7, -14⟩, ⟨-7, -14⟩, ⟨-5, -10⟩, ⟨-5, -10⟩, ⟨7, 14⟩, ⟨0, 0⟩, ⟨-5, -10⟩, ⟨9, 18⟩] = 8 := by eval_rank

#print axioms result
