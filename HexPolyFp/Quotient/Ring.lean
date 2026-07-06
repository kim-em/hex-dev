/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Enumeration

public section
set_option backward.proofsInPublic true

/-!
Quotient ring/field construction for `F_p[X] / (g)`: the `Quotient`
representative type, element enumeration, the ring operations and their
commutative-ring axioms, and the field inverse (valid for irreducible
`g`).
-/
namespace Hex
namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]

local instance : DensePoly.DivModLaws (ZMod64 p) :=
  ZMod64.instDivModLawsZMod64Fp p

/-- Canonical representatives for the quotient `F_p[X] / (g)`, reduced modulo
a monic positive-degree modulus. -/
structure Quotient (g : FpPoly p) (hmonic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) where
  /-- The chosen representative polynomial, of degree below `g`. -/
  val : FpPoly p
  /-- The representative's degree is strictly below that of the modulus `g`. -/
  reduced : val.degree?.getD 0 < g.degree?.getD 0

namespace Quotient

variable {g : FpPoly p} {hmonic : DensePoly.Monic g}
variable {hg_pos : 0 < g.degree?.getD 0}

omit [ZMod64.PrimeModulus p] in
/-- Two quotient elements are equal when their underlying representatives
agree; the extensionality principle for `Quotient g`. -/
@[ext] theorem ext {a b : Quotient g hmonic hg_pos} (h : a.val = b.val) :
    a = b := by
  cases a
  cases b
  simp at h
  subst h
  rfl

omit [ZMod64.PrimeModulus p] in
instance : DecidableEq (Quotient g hmonic hg_pos) := by
  intro a b
  match decEq a.val b.val with
  | isTrue h =>
      exact isTrue (ext h)
  | isFalse h =>
      exact isFalse (by
        intro hab
        exact h (congrArg Quotient.val hab))

/-- Reduce a polynomial to its canonical quotient representative. -/
@[expose]
def reduce (f : FpPoly p) : Quotient g hmonic hg_pos :=
  ⟨FpPoly.modByMonic g f hmonic, by
    rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    exact DensePoly.mod_degree_lt_of_pos_degree f g hg_pos⟩

/-- The stored representative of `reduce f` is the monic remainder computed by
the executable reduction path. -/
@[simp, grind =] theorem reduce_val (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val =
      FpPoly.modByMonic g f hmonic :=
  rfl

/-- The stored representative of `reduce f` is also the ordinary remainder
`f % g`, exposing the algebraic view used by congruence lemmas. -/
theorem reduce_val_eq_mod (f : FpPoly p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val = f % g := by
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/-- Polynomial congruence modulo the defining quotient polynomial. -/
@[expose]
def Congr (f h : FpPoly p) : Prop :=
  DensePoly.Congr f h g

/-- Congruent polynomials have the same canonical quotient representative. -/
theorem reduce_eq_reduce_of_congr {f h : FpPoly p} (hc : Congr (g := g) f h) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g hc

/-- Equal canonical quotient representatives imply congruence modulo the
defining polynomial. -/
theorem congr_of_reduce_eq_reduce {f h : FpPoly p}
    (heq :
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h) :
    Congr (g := g) f h := by
  unfold Congr
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  apply @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p) f h g
  have hval := congrArg Quotient.val heq
  have hf := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f
  have hh := reduce_val_eq_mod (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h
  rw [hf, hh] at hval
  exact hval

/-- Equality of reduced representatives is equivalent to congruence modulo the
quotient modulus. -/
theorem reduce_eq_reduce_iff_congr (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h ↔
      Congr (g := g) f h :=
  ⟨congr_of_reduce_eq_reduce, reduce_eq_reduce_of_congr⟩

namespace Internal

private theorem nodup_map_of_injective
    {α β : Type} {xs : List α} {f : α → β}
    (hxs : xs.Nodup)
    (hinj : ∀ a, a ∈ xs → ∀ b, b ∈ xs → f a = f b → a = b) :
    (xs.map f).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons]
      rw [List.nodup_cons] at hxs ⊢
      constructor
      · intro hx
        rcases List.mem_map.mp hx with ⟨y, hy, hxy⟩
        have hyx : y = x := hinj y (by simp [hy]) x (by simp) hxy
        exact hxs.1 (by simpa [hyx] using hy)
      · exact ih hxs.2 (by
          intro a ha b hb hab
          exact hinj a (by simp [ha]) b (by simp [hb]) hab)

private theorem length_filter_ne_eq_pred_of_mem_nodup
    {α : Type} [DecidableEq α] {z : α} :
    ∀ {xs : List α}, z ∈ xs → xs.Nodup →
      (xs.filter (fun a => decide (a ≠ z))).length = xs.length - 1
  | [], hmem, _ => by
      cases hmem
  | x :: xs, hmem, hnodup => by
      rw [List.nodup_cons] at hnodup
      by_cases hx : x = z
      · have hnot_mem : x ∉ xs := hnodup.1
        have hfilter : xs.filter (fun a => decide (a ≠ z)) = xs := by
          rw [List.filter_eq_self]
          intro a ha
          exact decide_eq_true (fun haz => hnot_mem (by simpa [hx, haz] using ha))
        rw [List.filter_cons_of_neg]
        · rw [hfilter]
          simp
        · simp [hx]
      · have hz_mem_xs : z ∈ xs := by
          cases hmem with
          | head =>
              exact False.elim (hx rfl)
          | tail _ hz =>
              exact hz
        have ih := length_filter_ne_eq_pred_of_mem_nodup hz_mem_xs hnodup.2
        have hlen_pos : 0 < xs.length := List.length_pos_of_mem hz_mem_xs
        rw [List.filter_cons_of_pos]
        · simp only [List.length_cons]
          rw [ih]
          omega
        · exact decide_eq_true hx

private theorem perm_of_nodup_mem_iff
    {α : Type} :
    ∀ {xs ys : List α}, xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → List.Perm xs ys
  | [], ys, _, _, hmem => by
      cases ys with
      | nil => exact .nil
      | cons y _ =>
          have hy : y ∈ ([] : List α) := (hmem y).mpr List.mem_cons_self
          exact absurd hy List.not_mem_nil
  | x :: xs', ys, hxs, hys, hmem => by
      have hxs_inv := List.nodup_cons.mp hxs
      have hx_not_in_xs' : x ∉ xs' := hxs_inv.1
      have hxs' : xs'.Nodup := hxs_inv.2
      have hx_mem : x ∈ ys := (hmem x).mp List.mem_cons_self
      obtain ⟨ys₁, ys₂, hys_eq⟩ := List.append_of_mem hx_mem
      subst hys_eq
      have hys_perm : List.Perm (ys₁ ++ x :: ys₂) (x :: (ys₁ ++ ys₂)) :=
        List.perm_middle
      have h_inner_nodup : (x :: (ys₁ ++ ys₂)).Nodup := hys_perm.nodup hys
      have h_inner_inv := List.nodup_cons.mp h_inner_nodup
      have hx_not_inner : x ∉ ys₁ ++ ys₂ := h_inner_inv.1
      have h_concat_nodup : (ys₁ ++ ys₂).Nodup := h_inner_inv.2
      have hmem' : ∀ a, a ∈ xs' ↔ a ∈ ys₁ ++ ys₂ := by
        intro a
        constructor
        · intro ha
          have ha_in_xs : a ∈ x :: xs' := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := (hmem a).mp ha_in_xs
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := hys_perm.mem_iff.mp ha_in_ys
          rcases List.mem_cons.mp ha_in_split with hax | h
          · exact absurd (hax ▸ ha) hx_not_in_xs'
          · exact h
        · intro ha
          have ha_in_split : a ∈ x :: (ys₁ ++ ys₂) := List.mem_cons.mpr (Or.inr ha)
          have ha_in_ys : a ∈ ys₁ ++ x :: ys₂ := hys_perm.mem_iff.mpr ha_in_split
          have ha_in_xs : a ∈ x :: xs' := (hmem a).mpr ha_in_ys
          rcases List.mem_cons.mp ha_in_xs with hax | h
          · exact absurd (hax ▸ ha) hx_not_inner
          · exact h
      have ih_perm := perm_of_nodup_mem_iff hxs' h_concat_nodup hmem'
      exact (ih_perm.cons x).trans hys_perm.symm

/-- All canonical quotient representatives, enumerated via bounded-degree
polynomials. -/
@[expose]
def elements : List (Quotient g hmonic hg_pos) :=
  (Enumeration.polysBelowDegree p (g.degree?.getD 0)).map
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos))

/-- `elements` enumerates exactly `p ^ deg g` canonical representatives —
the order of the quotient ring `FpPoly p / g`. -/
@[simp, grind =] theorem elements_length :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).length =
      p ^ g.degree?.getD 0 := by
  simp [elements]

/-- Every quotient element appears in `elements`. -/
theorem mem_elements (a : Quotient g hmonic hg_pos) :
    a ∈ elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos) := by
  unfold elements
  apply List.mem_map.mpr
  refine ⟨a.val, Enumeration.mem_polysBelowDegree_of_degree_getD_lt a.reduced, ?_⟩
  apply ext
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  exact DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced

/-- The quotient enumeration has no duplicate elements. -/
theorem elements_nodup :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).Nodup := by
  unfold elements
  apply nodup_map_of_injective
  · exact Enumeration.polysBelowDegree_nodup (p := p) (g.degree?.getD 0)
  · intro a ha b hb hab
    have hval := congrArg Quotient.val hab
    rw [reduce_val, reduce_val, FpPoly.modByMonic, FpPoly.modByMonic,
      DensePoly.modByMonic_eq_mod, DensePoly.modByMonic_eq_mod] at hval
    have ha_deg : a.degree?.getD 0 < g.degree?.getD 0 :=
      Enumeration.degree_getD_lt_of_mem_polysBelowDegree hg_pos ha
    have hb_deg : b.degree?.getD 0 < g.degree?.getD 0 :=
      Enumeration.degree_getD_lt_of_mem_polysBelowDegree hg_pos hb
    rw [DensePoly.mod_eq_self_of_degree_lt a g ha_deg,
      DensePoly.mod_eq_self_of_degree_lt b g hb_deg] at hval
    exact hval

/-- The quotient has `p ^ deg(g)` canonical representatives in the executable
list-cardinality sense. -/
theorem elements_card :
    (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).length =
      p ^ g.degree?.getD 0 :=
  elements_length (g := g) (hmonic := hmonic) (hg_pos := hg_pos)

end Internal

omit [ZMod64.PrimeModulus p] in
/-- Equality of quotient elements is equality of canonical remainders. -/
theorem eq_iff_val_eq {a b : Quotient g hmonic hg_pos} :
    a = b ↔ a.val = b.val :=
  ⟨fun h => by cases h; rfl, ext⟩

/-- Zero in the quotient. -/
@[expose]
def zero : Quotient g hmonic hg_pos :=
  reduce 0

instance : Zero (Quotient g hmonic hg_pos) where
  zero := zero

namespace Internal

/-- The nonzero quotient elements, as a concrete duplicate-free sublist of
`elements`. -/
@[expose]
def nonzeroElements : List (Quotient g hmonic hg_pos) :=
  (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
    (fun a => decide (a ≠ 0))

/-- Membership in `nonzeroElements` is exactly nonzero quotient membership. -/
theorem mem_nonzeroElements (a : Quotient g hmonic hg_pos) :
    a ∈ nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos) ↔
      a ≠ 0 := by
  simp [nonzeroElements, mem_elements a]

/-- The nonzero quotient enumeration has no duplicates. -/
theorem nonzeroElements_nodup :
    (nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).Nodup := by
  unfold nonzeroElements
  exact (elements_nodup (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter _

/-- There are `p ^ deg(g) - 1` nonzero quotient representatives. -/
theorem nonzeroElements_card :
    (nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).length =
      p ^ g.degree?.getD 0 - 1 := by
  unfold nonzeroElements
  rw [length_filter_ne_eq_pred_of_mem_nodup
    (mem_elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos) 0)
    (elements_nodup (g := g) (hmonic := hmonic) (hg_pos := hg_pos))]
  rw [elements_card]

end Internal

/-- One in the quotient. -/
@[expose]
def one : Quotient g hmonic hg_pos :=
  reduce 1

instance : One (Quotient g hmonic hg_pos) where
  one := one

/-- The class of the polynomial indeterminate. -/
@[expose]
def X : Quotient g hmonic hg_pos :=
  reduce FpPoly.X

/-- Addition of canonical quotient representatives. -/
@[expose]
def add (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val + b.val)

instance : Add (Quotient g hmonic hg_pos) where
  add := add

/-- Negation of canonical quotient representatives. -/
@[expose]
def neg (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (-a.val)

instance : Neg (Quotient g hmonic hg_pos) where
  neg := neg

/-- Subtraction of canonical quotient representatives. -/
@[expose]
def sub (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val - b.val)

instance : Sub (Quotient g hmonic hg_pos) where
  sub := sub

/-- Multiplication of canonical quotient representatives. -/
@[expose]
def mul (a b : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  reduce (a.val * b.val)

instance : Mul (Quotient g hmonic hg_pos) where
  mul := mul

/-- Natural-number powers in the quotient. -/
@[expose]
def pow (a : Quotient g hmonic hg_pos) : Nat → Quotient g hmonic hg_pos
  | 0 => 1
  | n + 1 => pow a n * a

instance : Pow (Quotient g hmonic hg_pos) Nat where
  pow := pow

/-- The stored representative of quotient zero is the reduction of the zero
polynomial. -/
@[simp, grind =] theorem zero_val :
    (0 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 0 hmonic :=
  rfl

/-- The stored representative of quotient one is the reduction of the constant
polynomial `1`. -/
@[simp, grind =] theorem one_val :
    (1 : Quotient g hmonic hg_pos).val = FpPoly.modByMonic g 1 hmonic :=
  rfl

/-- The stored representative of the quotient indeterminate is the reduced
polynomial variable. -/
@[simp, grind =] theorem X_val :
    (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).val =
      FpPoly.modByMonic g FpPoly.X hmonic :=
  rfl

/-- Addition of quotient elements reduces the sum of their canonical
representatives. -/
@[simp, grind =] theorem add_val (a b : Quotient g hmonic hg_pos) :
    (a + b).val = FpPoly.modByMonic g (a.val + b.val) hmonic :=
  rfl

/-- Negation of a quotient element reduces the negated representative. -/
@[simp, grind =] theorem neg_val (a : Quotient g hmonic hg_pos) :
    (-a).val = FpPoly.modByMonic g (-a.val) hmonic :=
  rfl

/-- Subtraction of quotient elements reduces the difference of their canonical
representatives. -/
@[simp, grind =] theorem sub_val (a b : Quotient g hmonic hg_pos) :
    (a - b).val = FpPoly.modByMonic g (a.val - b.val) hmonic :=
  rfl

/-- Multiplication of quotient elements reduces the product of their canonical
representatives. -/
@[simp, grind =] theorem mul_val (a b : Quotient g hmonic hg_pos) :
    (a * b).val = FpPoly.modByMonic g (a.val * b.val) hmonic :=
  rfl

/-- Zeroth quotient power is the multiplicative identity. -/
@[simp, grind =] theorem pow_zero (a : Quotient g hmonic hg_pos) :
    a ^ (0 : Nat) = 1 := by
  rfl

/-- Successor quotient powers multiply one more copy on the right. -/
@[simp, grind =] theorem pow_succ (a : Quotient g hmonic hg_pos) (n : Nat) :
    a ^ (n + 1) = a ^ n * a := by
  rfl

/-- Reducing a sum agrees with summing the separately reduced representatives
and reducing once more. -/
theorem reduce_add_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val +
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

/-- Reducing a product agrees with multiplying the separately reduced
representatives and reducing once more. -/
theorem reduce_mul_eq (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f * h) =
      reduce
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        ((reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).val *
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h).val) := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  rw [reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod, reduce_val_eq_mod]
  exact @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
    (ZMod64.instDivModLawsZMod64Fp p) f h g

/-- Reduction into the quotient preserves addition. -/
theorem reduce_add (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f +
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h :=
  reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h

/-- Reduction into the quotient preserves multiplication. -/
theorem reduce_mul (f h : FpPoly p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f * h) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f *
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h :=
  reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h

omit [ZMod64.PrimeModulus p] in
private theorem monomial_eq_C_mul_monomial_one (n : Nat) (c : ZMod64 p) :
    (DensePoly.monomial n c : FpPoly p) =
      DensePoly.C c * (DensePoly.monomial n (1 : ZMod64 p) : FpPoly p) := by
  rw [FpPoly.C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro i
  have hzero : c * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_monomial, DensePoly.coeff_scale _ _ _ hzero,
    DensePoly.coeff_monomial]
  split
  · grind
  · exact hzero.symm

/-- Reducing an already-canonical quotient representative leaves it unchanged. -/
theorem reduce_val_self (a : Quotient g hmonic hg_pos) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val = a := by
  apply ext
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  exact DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced

/-- The canonical quotient representative of `1` is the polynomial `1`. -/
theorem one_val_eq_one :
    (1 : Quotient g hmonic hg_pos).val = (1 : FpPoly p) := by
  rw [one_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  have hone_deg : (1 : FpPoly p).degree?.getD 0 < g.degree?.getD 0 := by
    change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 < g.degree?.getD 0
    simpa using hg_pos
  exact DensePoly.mod_eq_self_of_degree_lt (1 : FpPoly p) g hone_deg

/-- `1` is a left identity for quotient multiplication. -/
@[simp, grind =] theorem one_mul (a : Quotient g hmonic hg_pos) :
    (1 : Quotient g hmonic hg_pos) * a = a := by
  calc
    (1 : Quotient g hmonic hg_pos) * a =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((1 : Quotient g hmonic hg_pos).val * a.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((1 : FpPoly p) * a.val) := by rw [one_val_eq_one]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.one_mul]
    _ = a := reduce_val_self a

/-- `1` is a right identity for quotient multiplication. -/
@[simp, grind =] theorem mul_one (a : Quotient g hmonic hg_pos) :
    a * (1 : Quotient g hmonic hg_pos) = a := by
  calc
    a * (1 : Quotient g hmonic hg_pos) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (1 : Quotient g hmonic hg_pos).val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (1 : FpPoly p)) := by rw [one_val_eq_one]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.mul_one]
    _ = a := reduce_val_self a

/-- Quotient multiplication is associative. -/
theorem mul_assoc (a b c : Quotient g hmonic hg_pos) :
    (a * b) * c = a * (b * c) := by
  calc
    (a * b) * c =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a * b).val * c.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a.val * b.val) * c.val) := by
          have hmul := reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val * b.val) c.val
          rw [reduce_val_self c] at hmul
          exact hmul.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b.val * c.val)) := by rw [FpPoly.mul_assoc]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b * c).val) := by
          have hmul := reduce_mul_eq (g := g) (hmonic := hmonic)
            (hg_pos := hg_pos) a.val (b.val * c.val)
          rw [reduce_val_self a] at hmul
          exact hmul
    _ = a * (b * c) := rfl

/-- Quotient multiplication is commutative. -/
theorem mul_comm (a b : Quotient g hmonic hg_pos) :
    a * b = b * a := by
  calc
    a * b =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * b.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (b.val * a.val) := by rw [FpPoly.mul_comm]
    _ = b * a := rfl

/-- Quotient powers turn addition of exponents into multiplication. -/
theorem pow_add (a : Quotient g hmonic hg_pos) (m n : Nat) :
    a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
      simp [Nat.add_zero]
  | succ n ih =>
      calc
        a ^ (m + (n + 1)) = a ^ ((m + n) + 1) := by rw [Nat.add_succ]
        _ = a ^ (m + n) * a := by rfl
        _ = (a ^ m * a ^ n) * a := by rw [ih]
        _ = a ^ m * (a ^ n * a) := by rw [mul_assoc]
        _ = a ^ m * a ^ (n + 1) := by rfl

/-- Quotient powers turn multiplication of exponents into iterated powering. -/
theorem pow_mul (a : Quotient g hmonic hg_pos) (m n : Nat) :
    (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (a ^ m) ^ (n + 1) = (a ^ m) ^ n * a ^ m := by rfl
        _ = a ^ (m * n) * a ^ m := by rw [ih]
        _ = a ^ (m * n + m) := by
          exact (pow_add a (m * n) m).symm
        _ = a ^ (m * (n + 1)) := by rw [Nat.mul_succ]

/--
Reducing an executable polynomial power agrees with powering its quotient
class.
-/
theorem reduce_linearPow_eq_pow (f : FpPoly p) (n : Nat) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (FpPoly.linearPow f n) =
      (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (FpPoly.linearPow f (n + 1)) =
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (FpPoly.linearPow f n * f) := by
              rw [FpPoly.linearPow_succ]
        _ =
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (FpPoly.linearPow f n) *
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f := by
              exact reduce_mul_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (FpPoly.linearPow f n) f
        _ =
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ n *
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f := by
              rw [ih]
        _ =
          (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) ^ (n + 1) := by
              rfl

/--
The quotient class of the monomial `c * X^n` is the constant class `c`
times the `n`th power of the quotient indeterminate.
-/
theorem reduce_monomial_eq_const_mul_X_pow (n : Nat) (c : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial n c : FpPoly p) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ n := by
  calc
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial n c : FpPoly p) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C c * (DensePoly.monomial n (1 : ZMod64 p) : FpPoly p)) := by
          rw [monomial_eq_C_mul_monomial_one]
    _ =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (DensePoly.monomial n (1 : ZMod64 p) : FpPoly p) := by
          exact reduce_mul (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (DensePoly.C c) (DensePoly.monomial n (1 : ZMod64 p) : FpPoly p)
    _ =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
          (X (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) ^ n := by
          have hpow :=
            reduce_linearPow_eq_pow (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (FpPoly.X (p := p)) n
          change
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (FpPoly.linearPow (DensePoly.monomial 1 (1 : ZMod64 p)) n) =
              (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.monomial 1 (1 : ZMod64 p))) ^ n at hpow
          rw [FpPoly.linearPow_monomial_one] at hpow
          exact congrArg
            (fun q : Quotient g hmonic hg_pos =>
              reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) * q)
            hpow

/-- `0` is a right identity for addition in the quotient ring. -/
@[simp, grind =] theorem add_zero (a : Quotient g hmonic hg_pos) :
    a + (0 : Quotient g hmonic hg_pos) = a := by
  calc
    a + (0 : Quotient g hmonic hg_pos) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + (0 : Quotient g hmonic hg_pos).val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + (0 : FpPoly p)) := by
          rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.add_zero]
    _ = a := reduce_val_self a

/-- `0` is a left identity for addition in the quotient ring. -/
@[simp, grind =] theorem zero_add (a : Quotient g hmonic hg_pos) :
    (0 : Quotient g hmonic hg_pos) + a = a := by
  calc
    (0 : Quotient g hmonic hg_pos) + a =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((0 : Quotient g hmonic hg_pos).val + a.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((0 : FpPoly p) + a.val) := by
          rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.zero_add]
    _ = a := reduce_val_self a

/-- Quotient addition is associative.  Together with `add_zero`, `zero_add`,
`add_comm` and `add_left_neg` this supplies the additive-group axioms behind the
`Field (Quotient g hmonic hg_pos)` instance. -/
theorem add_assoc (a b c : Quotient g hmonic hg_pos) :
    (a + b) + c = a + (b + c) := by
  calc
    (a + b) + c =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a + b).val + c.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a.val + b.val) + c.val) := by
          have hadd := reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val + b.val) c.val
          rw [reduce_val_self c] at hadd
          exact hadd.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + (b.val + c.val)) := by rw [FpPoly.add_assoc]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + (b + c).val) := by
          have hadd := reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            a.val (b.val + c.val)
          rw [reduce_val_self a] at hadd
          exact hadd
    _ = a + (b + c) := rfl

/-- Quotient addition is commutative. -/
theorem add_comm (a b : Quotient g hmonic hg_pos) :
    a + b = b + a := by
  calc
    a + b =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + b.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (b.val + a.val) := by rw [FpPoly.add_comm]
    _ = b + a := rfl

private theorem add_pair_swap_quot (a b c d : Quotient g hmonic hg_pos) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [add_assoc a b (c + d), ← add_assoc b c d, add_comm b c, add_assoc c b d,
    ← add_assoc a c (b + d)]

/-- Adding a quotient element to its left additive inverse gives zero. -/
@[simp, grind =] theorem add_left_neg (a : Quotient g hmonic hg_pos) :
    -a + a = 0 := by
  calc
    -a + a =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((-a).val + a.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (-a.val + a.val) := by
          have h :=
            reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              (-a.val) a.val
          rw [reduce_val_self a] at h
          exact h.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (0 : FpPoly p) := by
          rw [FpPoly.add_left_neg]
    _ = 0 := rfl

/-- Adding the right additive inverse of a quotient element gives zero. -/
@[simp, grind =] theorem add_right_neg (a : Quotient g hmonic hg_pos) :
    a + -a = 0 := by
  rw [add_comm]
  exact add_left_neg a

/-- Quotient subtraction is addition of the right additive inverse. -/
theorem sub_eq_add_neg (a b : Quotient g hmonic hg_pos) :
    a - b = a + -b := by
  calc
    a - b =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val - b.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + -b.val) := by
          rw [FpPoly.sub_eq_add_neg]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val + (-b).val) := by
          have h :=
            reduce_add_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
              a.val (-b.val)
          rw [reduce_val_self a] at h
          exact h
    _ = a + -b := rfl

/-- Subtracting a quotient element from itself gives zero. -/
@[simp, grind =] theorem sub_self (a : Quotient g hmonic hg_pos) :
    a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

/-- A quotient subtraction is zero exactly when its left and right terms are
equal. -/
theorem sub_eq_zero_iff_eq {a b : Quotient g hmonic hg_pos} :
    a - b = 0 ↔ a = b := by
  constructor
  · intro hsub
    calc
      a = a + 0 := (add_zero a).symm
      _ = a + (-b + b) := by rw [add_left_neg]
      _ = (a + -b) + b := (add_assoc a (-b) b).symm
      _ = (a - b) + b := by rw [sub_eq_add_neg]
      _ = 0 + b := by rw [hsub]
      _ = b := zero_add b
  · intro h
    cases h
    exact sub_self a

/-- Distinct quotient elements have nonzero difference. -/
theorem sub_ne_zero_of_ne {a b : Quotient g hmonic hg_pos} (h : a ≠ b) :
    a - b ≠ 0 := by
  intro hzero
  exact h (sub_eq_zero_iff_eq.mp hzero)

/-- A nonzero quotient difference witnesses distinct quotient elements. -/
theorem ne_of_sub_ne_zero {a b : Quotient g hmonic hg_pos} (h : a - b ≠ 0) :
    a ≠ b := by
  intro hab
  apply h
  exact sub_eq_zero_iff_eq.mpr hab

/-- Subtracting zero leaves a quotient element unchanged. -/
@[simp, grind =] theorem sub_zero (a : Quotient g hmonic hg_pos) :
    a - (0 : Quotient g hmonic hg_pos) = a := by
  calc
    a - (0 : Quotient g hmonic hg_pos) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val - (0 : Quotient g hmonic hg_pos).val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val - (0 : FpPoly p)) := by
          rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a.val := by
          rw [FpPoly.sub_zero]
    _ = a := reduce_val_self a

/-- Quotient multiplication distributes over addition on the left. -/
theorem left_distrib (a b c : Quotient g hmonic hg_pos) :
    a * (b + c) = a * b + a * c := by
  calc
    a * (b + c) =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b + c).val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * (b.val + c.val)) := by
          have hmul := reduce_mul (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            a.val (b.val + c.val)
          rw [reduce_val_self a] at hmul
          exact hmul.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * b.val + a.val * c.val) := by rw [FpPoly.left_distrib]
    _ =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (a.val * b.val) +
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (a.val * c.val) := by
          exact reduce_add (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val * b.val) (a.val * c.val)
    _ = a * b + a * c := rfl

/-- Quotient multiplication distributes over addition on the right. -/
theorem right_distrib (a b c : Quotient g hmonic hg_pos) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a + b).val * c.val) := rfl
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((a.val + b.val) * c.val) := by
          have hmul := reduce_mul (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val + b.val) c.val
          rw [reduce_val_self c] at hmul
          exact hmul.symm
    _ = reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (a.val * c.val + b.val * c.val) := by rw [FpPoly.right_distrib]
    _ =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (a.val * c.val) +
          reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (b.val * c.val) := by
          exact reduce_add (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (a.val * c.val) (b.val * c.val)
    _ = a * c + b * c := rfl

/-- The xgcd-based inverse candidate, normalized by the leading coefficient of
the computed gcd. -/
@[expose]
def inverseCandidate (a : FpPoly p) : FpPoly p :=
  DensePoly.scale (DensePoly.leadingCoeff (DensePoly.gcd a g))⁻¹
    (DensePoly.xgcd a g).left

/--
Narrow Euclidean obligation for quotient inversion.

For a nonzero canonical representative modulo a monic irreducible positive-degree
polynomial, the normalized left Bezout coefficient is a multiplicative inverse
modulo `g`.
-/
theorem mul_mod_inverseCandidate_eq_one_of_irreducible
    (hg_irr : FpPoly.Irreducible g) {a : FpPoly p}
    (ha_ne : a ≠ 0) (ha_reduced : a.degree?.getD 0 < g.degree?.getD 0) :
    (a * inverseCandidate (g := g) a) % g = (1 : FpPoly p) % g := by
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  -- Bezout identity from the executable extended gcd.
  let xres : DensePoly.XGCDResult (ZMod64 p) := DensePoly.xgcd a g
  let d : FpPoly p := DensePoly.gcd a g
  have hbezout : xres.left * a + xres.right * g = d := by
    have hb := DensePoly.xgcd_bezout a g
    simpa [xres, d, DensePoly.gcd_eq_xgcd_gcd] using hb
  -- The gcd divides both inputs.
  have hda : d ∣ a := DensePoly.gcd_dvd_left a g
  have hdg : d ∣ g := DensePoly.gcd_dvd_right a g
  have hg_ne : g ≠ 0 := hg_irr.1
  have hd_ne : d ≠ 0 := by
    intro hzero
    obtain ⟨s, hs⟩ := hda
    apply ha_ne
    rw [hs, hzero, FpPoly.zero_mul]
  -- Irreducibility forces the gcd to be a unit constant.
  obtain ⟨r, hr⟩ := hdg
  have hr_ne : r ≠ 0 := by
    intro hzero
    apply hg_ne
    rw [hr, hzero, FpPoly.mul_zero]
  have hd_deg : d.degree? = some 0 := by
    rcases hg_irr.2 _ _ hr.symm with hd_deg_zero | hr_deg_zero
    · exact hd_deg_zero
    · exfalso
      have hsum : g.degree?.getD 0 = d.degree?.getD 0 + r.degree?.getD 0 := by
        rw [hr]
        exact FpPoly.degree?_mul_eq_add_degree? d r hd_ne hr_ne
      have hr_deg_zero' : r.degree?.getD 0 = 0 := by simp [hr_deg_zero]
      obtain ⟨s, hs⟩ := hda
      have hs_ne : s ≠ 0 := by
        intro hzero
        apply ha_ne
        rw [hs, hzero, FpPoly.mul_zero]
      have hsum_a : a.degree?.getD 0 = d.degree?.getD 0 + s.degree?.getD 0 := by
        rw [hs]
        exact FpPoly.degree?_mul_eq_add_degree? d s hd_ne hs_ne
      omega
  -- Extract the leading coefficient and verify it is invertible.
  let dlc : ZMod64 p := DensePoly.leadingCoeff d
  have hd_size : d.size = 1 := by
    unfold DensePoly.degree? at hd_deg
    by_cases hsize : d.size = 0
    · simp [hsize] at hd_deg
    · simp [hsize] at hd_deg
      omega
  have hd_size_pos : 0 < d.size := by omega
  have hdlc_ne : dlc ≠ 0 := by
    show DensePoly.leadingCoeff d ≠ 0
    rw [FpPoly.leadingCoeff_eq_coeff_pred d hd_size_pos]
    exact DensePoly.coeff_last_ne_zero_of_pos_size d hd_size_pos
  -- Scale Bezout by `dlc⁻¹` so the gcd becomes the unit `1`.
  let R : FpPoly p := DensePoly.scale dlc⁻¹ xres.right
  let L : FpPoly p := DensePoly.scale dlc⁻¹ xres.left
  have hbezout_scaled : L * a + R * g = DensePoly.scale dlc⁻¹ d := by
    show DensePoly.scale dlc⁻¹ xres.left * a +
        DensePoly.scale dlc⁻¹ xres.right * g = DensePoly.scale dlc⁻¹ d
    rw [← FpPoly.scale_mul_left, ← FpPoly.scale_mul_left,
        ← FpPoly.scale_add, hbezout]
  have hscale_d : DensePoly.scale dlc⁻¹ d = (1 : FpPoly p) := by
    apply DensePoly.ext_coeff
    intro n
    have hzero_mul : (dlc⁻¹ : ZMod64 p) * 0 = 0 := by grind
    rw [DensePoly.coeff_scale dlc⁻¹ d n hzero_mul]
    change dlc⁻¹ * d.coeff n = (DensePoly.C (1 : ZMod64 p)).coeff n
    rw [DensePoly.coeff_C]
    cases n with
    | zero =>
        have hd_coeff : d.coeff 0 = dlc := by
          show d.coeff 0 = DensePoly.leadingCoeff d
          rw [FpPoly.leadingCoeff_eq_coeff_pred d hd_size_pos]
          congr 1
          omega
        rw [hd_coeff]
        simp
        exact ZMod64.inv_mul_eq_one_of_prime
          (ZMod64.PrimeModulus.prime (p := p)) hdlc_ne
    | succ k =>
        have hd_coeff : d.coeff (k + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le d (by omega)
        rw [hd_coeff]
        have hkne : k + 1 ≠ 0 := Nat.succ_ne_zero k
        rw [if_neg hkne]
        exact hzero_mul
  have hkey : L * a + R * g = (1 : FpPoly p) := by
    show DensePoly.scale dlc⁻¹ xres.left * a +
        DensePoly.scale dlc⁻¹ xres.right * g = (1 : FpPoly p)
    rw [hbezout_scaled, hscale_d]
  -- Convert to the required modular identity using mod_add_mod and mod_mul_self.
  have hRg_mod : (R * g) % g = 0 := by
    show (DensePoly.scale dlc⁻¹ xres.right * g) % g = 0
    rw [FpPoly.mul_comm (DensePoly.scale dlc⁻¹ xres.right) g]
    exact DensePoly.mod_eq_zero_of_dvd (g * DensePoly.scale dlc⁻¹ xres.right) g ⟨_, rfl⟩
  have hL_eq : inverseCandidate (g := g) a = L := rfl
  rw [hL_eq, FpPoly.mul_comm a L]
  -- Goal: L * a % g = 1 % g
  have hmm : L * a % g % g = L * a % g :=
    @DensePoly.mod_mod (ZMod64 p) inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) (L * a) g
  have hadd : (L * a + R * g) % g = (L * a % g + R * g % g) % g :=
    @DensePoly.mod_add_mod (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) (L * a) (R * g) g
  calc L * a % g
      = L * a % g % g := hmm.symm
    _ = (L * a % g + 0) % g := by rw [FpPoly.add_zero]
    _ = (L * a % g + R * g % g) % g := by rw [hRg_mod]
    _ = (L * a + R * g) % g := hadd.symm
    _ = 1 % g := by rw [hkey]

/-- Multiplicative inverse candidate in the quotient, with the conventional
junk value `0⁻¹ = 0`.  The cancellation theorem below requires irreducibility. -/
@[expose]
def inv (a : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  if a.val = 0 then
    0
  else
    reduce (inverseCandidate (g := g) a.val)

instance : Inv (Quotient g hmonic hg_pos) where
  inv := inv

/-- The inverse of `0` is `0`, the conventional junk value fixed by `inv`.  This
is the `inv_zero` field axiom required by `Field`; it holds unconditionally and,
unlike `mul_inv_cancel`, needs no irreducibility hypothesis. -/
theorem inv_zero :
    (0 : Quotient g hmonic hg_pos)⁻¹ = 0 := by
  have hzero_val : (0 : Quotient g hmonic hg_pos).val = 0 := by
    rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
  change inv (0 : Quotient g hmonic hg_pos) = 0
  unfold inv
  change (if (0 : Quotient g hmonic hg_pos).val = 0 then 0
    else reduce (inverseCandidate (g := g) (0 : Quotient g hmonic hg_pos).val)) = 0
  rw [hzero_val]
  simp

/-- Multiplicative cancellation: when `g` is irreducible, every nonzero quotient
element `a` satisfies `a * a⁻¹ = 1`.  This is the field-inverse axiom that
promotes `Quotient g hmonic hg_pos` from a commutative ring to a `Field`; the
`FpPoly.Irreducible g` hypothesis is essential, since for reducible `g` a nonzero
zero-divisor has no inverse. -/
theorem mul_inv_cancel (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have ha_val_ne : a.val ≠ 0 := by
    intro hval
    apply ha
    apply ext
    change a.val = (0 : Quotient g hmonic hg_pos).val
    simpa [zero, reduce_val_eq_mod, hval, FpPoly.modByMonic] using
      (DensePoly.modByMonic_zero g hmonic).symm
  apply ext
  change (a * inv (g := g) (hmonic := hmonic) (hg_pos := hg_pos) a).val =
    (1 : Quotient g hmonic hg_pos).val
  unfold inv
  simp [ha_val_ne]
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  change FpPoly.modByMonic g
      (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
      hmonic =
    FpPoly.modByMonic g 1 hmonic
  calc
    FpPoly.modByMonic g
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic)
        hmonic =
        (a.val * FpPoly.modByMonic g (inverseCandidate (g := g) a.val) hmonic) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * ((inverseCandidate (g := g) a.val) % g)) % g := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
    _ = (a.val * inverseCandidate (g := g) a.val) % g := by
          have ha_mod : a.val % g = a.val :=
            DensePoly.mod_eq_self_of_degree_lt a.val g a.reduced
          have hmul_mod :=
            @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance inferInstance
              (ZMod64.instDivModLawsZMod64Fp p) a.val
              (inverseCandidate (g := g) a.val) g
          calc
            (a.val * ((inverseCandidate (g := g) a.val) % g)) % g =
                ((a.val % g) * ((inverseCandidate (g := g) a.val) % g)) % g := by
                  simp [ha_mod]
            _ = (a.val * inverseCandidate (g := g) a.val) % g := hmul_mod.symm
    _ = (1 : FpPoly p) % g :=
          mul_mod_inverseCandidate_eq_one_of_irreducible
            (g := g) hg_irr ha_val_ne a.reduced
    _ = FpPoly.modByMonic g 1 hmonic := by
          rw [FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]

/-- The inverse candidate also cancels on the left for nonzero quotient
elements modulo an irreducible polynomial. -/
theorem inv_mul_cancel (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a⁻¹ * a = 1 := by
  rw [mul_comm]
  exact mul_inv_cancel (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr ha

/-- Multiplying any quotient element by zero gives zero. -/
@[simp, grind =] theorem mul_zero (a : Quotient g hmonic hg_pos) :
    a * (0 : Quotient g hmonic hg_pos) = 0 := by
  apply ext
  letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hzero_val : (0 : Quotient g hmonic hg_pos).val = (0 : FpPoly p) := by
    rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
  show FpPoly.modByMonic g (a.val * (0 : Quotient g hmonic hg_pos).val) hmonic =
    (0 : Quotient g hmonic hg_pos).val
  rw [hzero_val, FpPoly.mul_zero, FpPoly.modByMonic, DensePoly.modByMonic_zero]

/-- Zero times any quotient element is zero. -/
@[simp, grind =] theorem zero_mul (a : Quotient g hmonic hg_pos) :
    (0 : Quotient g hmonic hg_pos) * a = 0 := by
  rw [mul_comm]
  exact mul_zero a

/-- Addition on the left by a fixed quotient element is cancellative. -/
theorem add_left_cancel (a b c : Quotient g hmonic hg_pos)
    (h : a + b = a + c) : b = c := by
  calc
    b = 0 + b := (zero_add b).symm
    _ = (-a + a) + b := by rw [add_left_neg]
    _ = -a + (a + b) := add_assoc (-a) a b
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc (-a) a c).symm
    _ = 0 + c := by rw [add_left_neg]
    _ = c := zero_add c

/-- Addition on the right by a fixed quotient element is cancellative. -/
theorem add_right_cancel (a b c : Quotient g hmonic hg_pos)
    (h : b + a = c + a) : b = c := by
  apply add_left_cancel a
  rw [add_comm a b, add_comm a c]
  exact h

/-- If two quotient elements add to zero, the left element is the negative of
the right element. -/
theorem eq_neg_of_add_eq_zero {a b : Quotient g hmonic hg_pos}
    (h : a + b = 0) : a = -b := by
  calc
    a = a + 0 := (add_zero a).symm
    _ = a + (b + -b) := by rw [add_right_neg]
    _ = (a + b) + -b := (add_assoc a b (-b)).symm
    _ = 0 + -b := by rw [h]
    _ = -b := zero_add (-b)

/-- If two quotient elements add to zero, the right element is the negative of
the left element. -/
theorem eq_neg_of_add_eq_zero_right {a b : Quotient g hmonic hg_pos}
    (h : a + b = 0) : b = -a := by
  apply eq_neg_of_add_eq_zero
  rw [add_comm]
  exact h

/-- Adding back the right-hand subtrahend cancels quotient subtraction. -/
@[simp, grind =] theorem sub_add_cancel (a b : Quotient g hmonic hg_pos) :
    a - b + b = a := by
  rw [sub_eq_add_neg]
  calc
    (a + -b) + b = a + (-b + b) := add_assoc a (-b) b
    _ = a + 0 := by rw [add_left_neg]
    _ = a := add_zero a

/-- Subtracting the right-hand addend cancels quotient addition. -/
@[simp, grind =] theorem add_sub_cancel_right (a b : Quotient g hmonic hg_pos) :
    a + b - b = a := by
  rw [sub_eq_add_neg]
  calc
    (a + b) + -b = a + (b + -b) := add_assoc a b (-b)
    _ = a + 0 := by rw [add_right_neg]
    _ = a := add_zero a

/-- Subtracting the left-hand addend cancels quotient addition. -/
@[simp, grind =] theorem add_sub_cancel_left (a b : Quotient g hmonic hg_pos) :
    a + b - a = b := by
  rw [add_comm a b]
  exact add_sub_cancel_right b a

/-- Multiplication by a negated quotient element on the right negates the
product. -/
theorem mul_neg_right (a b : Quotient g hmonic hg_pos) :
    a * -b = -(a * b) := by
  apply eq_neg_of_add_eq_zero
  calc
    a * -b + a * b = a * (-b + b) := (left_distrib a (-b) b).symm
    _ = a * 0 := by rw [add_left_neg]
    _ = 0 := mul_zero a

/-- Multiplication by a negated quotient element on the left negates the
product. -/
theorem neg_mul_left (a b : Quotient g hmonic hg_pos) :
    -a * b = -(a * b) := by
  calc
    -a * b = b * -a := mul_comm (-a) b
    _ = -(b * a) := mul_neg_right b a
    _ = -(a * b) := by rw [mul_comm b a]

/-- Quotient multiplication distributes over subtraction on the left. -/
theorem mul_sub (a b c : Quotient g hmonic hg_pos) :
    a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg b c, sub_eq_add_neg (a * b) (a * c), left_distrib,
    mul_neg_right]

/-- Quotient multiplication distributes over subtraction on the right. -/
theorem sub_mul (a b c : Quotient g hmonic hg_pos) :
    (a - b) * c = a * c - b * c := by
  rw [sub_eq_add_neg a b, sub_eq_add_neg (a * c) (b * c), right_distrib,
    neg_mul_left]

/-- Adjacent quotient subtractions cancel their shared middle term. -/
theorem sub_add_sub_cancel (a b c : Quotient g hmonic hg_pos) :
    (a - b) + (b - c) = a - c := by
  rw [sub_eq_add_neg a b, sub_eq_add_neg b c, sub_eq_add_neg a c]
  calc
    (a + -b) + (b + -c) = a + (-b + (b + -c)) := add_assoc a (-b) (b + -c)
    _ = a + ((-b + b) + -c) := by rw [add_assoc (-b) b (-c)]
    _ = a + (0 + -c) := by rw [add_left_neg]
    _ = a + -c := by rw [zero_add]

end Quotient
end FpPoly
end Hex
