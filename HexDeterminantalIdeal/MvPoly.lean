/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdeal.Rank
public import HexMvPoly

public section

/-!
Specialisation of a polynomial matrix at a point, its rank there, and the
rank-drop locus `InLocus r A p`: the point `p` lies in the zero set of the
determinantal ideal `I_r(A)`. The theorem `rankAt A p < r ↔ InLocus r A p`
needs evaluation to commute with the determinant, a ring-homomorphism
property proved in the Mathlib companion; this module ships the executable
definitions, the `Decidable` instance and the unfolding lemmas.
-/

namespace Hex
universe u
namespace Matrix

variable {k : Nat} {R : Type u} {cmp : Mono k → Mono k → Ordering}
  [Std.TransCmp cmp] [Std.LawfulEqCmp cmp] {n m : Nat}

/-- Evaluate every entry of a polynomial matrix at the point `p`. -/
@[expose]
def specialize [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) : Matrix R n m :=
  A.map (MvPoly.eval p)

/-- Entry formula for the specialised matrix. -/
@[grind =] theorem specialize_getElem [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) (i : Fin n) (j : Fin m) :
    (specialize A p)[i][j] = MvPoly.eval p A[i][j] := by
  unfold specialize
  rw [getElem_map]

/-- The rank of the polynomial matrix at the point `p`: row reduction of the
specialised matrix over the field. -/
@[expose]
def rankAt {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (A : Matrix (MvPoly k F cmp) n m) (p : Fin k → F) : Nat :=
  rowReduce_rank (specialize A p)

/-- `rankAt` unfolds to the row-reduction rank of the specialisation. -/
theorem rankAt_eq {F : Type u} [Lean.Grind.Field F] [DecidableEq F]
    (A : Matrix (MvPoly k F cmp) n m) (p : Fin k → F) :
    rankAt A p = rowReduce_rank (specialize A p) :=
  rfl

/-- The point `p` lies in the zero set of `I_r(A)`: every `r × r` minor of `A`
vanishes at `p`. -/
@[expose]
def InLocus [Lean.Grind.CommRing R] [DecidableEq R]
    (r : Nat) (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) : Prop :=
  ∀ M ∈ minors r A, MvPoly.eval p M = 0

instance [Lean.Grind.CommRing R] [DecidableEq R]
    (r : Nat) (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) :
    Decidable (InLocus r A p) :=
  inferInstanceAs (Decidable (∀ M ∈ minors r A, MvPoly.eval p M = 0))

/-- `InLocus` unfolds to the vanishing of every minor at the point. -/
theorem inLocus_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (r : Nat) (A : Matrix (MvPoly k R cmp) n m) (p : Fin k → R) :
    InLocus r A p ↔ ∀ M ∈ minors r A, MvPoly.eval p M = 0 :=
  Iff.rfl

end Matrix
end Hex
