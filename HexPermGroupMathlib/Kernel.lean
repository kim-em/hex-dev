/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Kernel.Assemble
public import HexPermGroupMathlib.Order

public section

/-! Mathlib translations of the Mathlib-free kernel certificate theorems. -/

namespace Hex.PermGroup.Kernel

variable {n : Nat}

/-- An accepted certificate decides membership in Mathlib's closure. -/
theorem sift_mem_iff {S : Array (Perm n)} {c : Certificate}
    (h : check n (S.toList.map pack) c = true) (p : Perm n) :
    Kernel.sift n (width n) (ident n (width n)) c (pack p) = true ↔ p.toEquiv ∈ closure S :=
  (sift_pack_iff h p).trans generated_iff_mem

/-- An accepted certificate gives the cardinality of Mathlib's closure. -/
theorem card_closure {S : Array (Perm n)} {c : Certificate}
    (h : check n (S.toList.map pack) c = true) : Nat.card (closure S) = order c :=
  hasOrder_iff_card.mp (order_of_check h)

/-- A Mathlib permutation from its literal images. The checked constructor and
its packing proof belong to the computational library. -/
@[expose] def permOfImages (n : Nat) (l : List Nat) : Equiv.Perm (Fin n) :=
  (Perm.ofImages n l).toEquiv

theorem pack_ofEquiv_permOfImages {n : Nat} {l : List Nat} (h : imagesOk n l = true) :
    pack (Perm.ofEquiv (permOfImages n l)) = packList n l := by
  simpa only [permOfImages, Perm.ofEquiv_toEquiv] using pack_ofImages h

/-- The image-list API retained for certificate sources produced by earlier releases. -/
def images (n : Nat) (g : Equiv.Perm (Fin n)) : List Nat :=
  (List.finRange n).map fun i => (g i).val

export Hex.PermGroup (setOf_mem_cons setOf_mem_singleton setOf_mem_nil
  closure_ofEquiv card_of_hasOrder mem_of_generated not_mem_of_neg)

theorem eq_top_of_hasOrder {gs : List (Equiv.Perm (Fin n))}
    (h : HasOrder (gs.map Perm.ofEquiv).toArray n.factorial) :
    Subgroup.closure {x | x ∈ gs} = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top, card_of_hasOrder h, Nat.card_perm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-! Compatibility assembly lemmas for reusable certificate sources. Their
soundness is supplied entirely by the computational library. -/

theorem map_pack_nil : (([] : List (Equiv.Perm (Fin n))).map Perm.ofEquiv).map pack = [] :=
  rfl

theorem map_pack_cons {g : Equiv.Perm (Fin n)} {gs : List (Equiv.Perm (Fin n))} {x : Nat}
    {xs : List Nat} (h : pack (Perm.ofEquiv g) = x) (t : (gs.map Perm.ofEquiv).map pack = xs) :
    ((g :: gs).map Perm.ofEquiv).map pack = x :: xs := by
  simp [h, ← t]

theorem check_gs {gs : List (Equiv.Perm (Fin n))} {inputs : List Nat} {c : Certificate}
    (hS : (gs.map Perm.ofEquiv).map pack = inputs) (h : check n inputs c = true) :
    check n ((gs.map Perm.ofEquiv).toArray.toList.map pack) c = true := by
  simpa [hS] using h

theorem card_of_check {gs : List (Equiv.Perm (Fin n))} {inputs : List Nat} {c : Certificate}
    {N : Nat} (hS : (gs.map Perm.ofEquiv).map pack = inputs) (h : check n inputs c = true)
    (hN : order c = N) : Nat.card (Subgroup.closure {x | x ∈ gs}) = N := by
  rw [← closure_ofEquiv, card_closure (check_gs hS h), hN]

theorem mem_of_check {gs : List (Equiv.Perm (Fin n))} {inputs : List Nat} {c : Certificate}
    {g : Equiv.Perm (Fin n)} {x : Nat} (hS : (gs.map Perm.ofEquiv).map pack = inputs)
    (h : check n inputs c = true) (hx : pack (Perm.ofEquiv g) = x)
    (hs : Kernel.sift n (width n) (ident n (width n)) c x = true) :
    g ∈ Subgroup.closure {x | x ∈ gs} := by
  rw [← closure_ofEquiv]
  have := (sift_mem_iff (check_gs hS h) (Perm.ofEquiv g)).mp (hx ▸ hs)
  simpa using this

theorem not_mem_of_check {gs : List (Equiv.Perm (Fin n))} {inputs : List Nat} {c : Certificate}
    {g : Equiv.Perm (Fin n)} {x : Nat} (hS : (gs.map Perm.ofEquiv).map pack = inputs)
    (h : check n inputs c = true) (hx : pack (Perm.ofEquiv g) = x)
    (hs : Kernel.sift n (width n) (ident n (width n)) c x = false) :
    g ∉ Subgroup.closure {x | x ∈ gs} := by
  rw [← closure_ofEquiv]
  intro hg
  have := (sift_mem_iff (check_gs hS h) (Perm.ofEquiv g)).mpr (by simpa using hg)
  rw [hx, hs] at this
  exact Bool.false_ne_true this

theorem eq_top_of_check {gs : List (Equiv.Perm (Fin n))} {inputs : List Nat} {c : Certificate}
    (hS : (gs.map Perm.ofEquiv).map pack = inputs) (h : check n inputs c = true)
    (hN : order c = n.factorial) : Subgroup.closure {x | x ∈ gs} = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top, card_of_check hS h hN, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end Hex.PermGroup.Kernel
