/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm

public section

/-!
Compiled implementations of permutation operations.

`Perm.comp` is defined through `Hex.Vector.ofFn'` and `Perm.inv` through a fold
over `List.finRange`, so that the kernel reduces them structurally. Compiled,
`comp` calls a closure for every image and `inv` allocates the list of points
and an identity vector for every inversion. The `@[csimp]` lemmas below replace
them, in compiled code only, by single array passes. The kernel and all proofs
keep the original definitions. Code compiled before this module is imported,
including `HexGraphIso`, which imports only `HexPermGroup.Perm`, keeps the
original compiled forms.
-/

namespace Hex.Perm

variable {n : Nat}

/-- The image vector of `p.comp q`, as one pass over `q`'s images. -/
def compVec (p q : Perm n) : Vector (Fin n) n :=
  ⟨q.vec.toArray.map fun j => p.vec[j], by simp⟩

theorem compVec_eq (p q : Perm n) : compVec p q = (p.comp q).vec := by
  apply Vector.ext
  intro i hi
  have := get_comp p q ⟨i, hi⟩
  simp only [get, Fin.getElem_fin] at this
  simp [compVec, this]

/-- `Perm.comp` for compiled code. -/
def compImpl (p q : Perm n) : Perm n :=
  ⟨compVec p q, compVec_eq p q ▸ (p.comp q).nodup, compVec_eq p q ▸ (p.comp q).complete⟩

@[csimp] theorem comp_eq_compImpl : @comp = @compImpl := by
  funext n p q
  exact ext_vec (compVec_eq p q).symm

/-- `invVec` for compiled code: the same scatter pass as a `Fin.foldl`, with no
intermediate list. It starts from `p`'s own image vector rather than the
identity, since the pass writes every position. -/
def invVecImpl (p : Perm n) : Vector (Fin n) n :=
  Fin.foldl n p.scatterStep p.vec

/-- A scatter pass over every point writes every position, so its result does not
depend on the starting vector. -/
theorem scatter_finRange_eq (p : Perm n) (v w : Vector (Fin n) n) :
    (List.finRange n).foldl p.scatterStep v = (List.finRange n).foldl p.scatterStep w := by
  apply Vector.ext
  intro k hk
  have e : (p.get (p.preimage ⟨k, hk⟩)).val = k := by simp
  have h1 := scatter_get p (List.finRange n) v (i := p.preimage ⟨k, hk⟩) (List.mem_finRange _)
  have h2 := scatter_get p (List.finRange n) w (i := p.preimage ⟨k, hk⟩) (List.mem_finRange _)
  simp only [e] at h1 h2
  exact h1.trans h2.symm

@[csimp] theorem invVec_eq_invVecImpl : @invVec = @invVecImpl := by
  funext n p
  rw [invVec, invVecImpl, ← Fin.foldl_eq_finRange_foldl, Fin.foldl_eq_finRange_foldl,
    Fin.foldl_eq_finRange_foldl]
  exact scatter_finRange_eq p _ _

/-- `Perm.inv` for compiled code. -/
def invImpl (p : Perm n) : Perm n :=
  ⟨invVecImpl p, invVec_eq_invVecImpl ▸ p.inv.nodup, invVec_eq_invVecImpl ▸ p.inv.complete⟩

@[csimp] theorem inv_eq_invImpl : @inv = @invImpl := by
  funext n p
  apply ext_vec
  show p.invVec = invVecImpl p
  rw [invVec_eq_invVecImpl]

end Hex.Perm
