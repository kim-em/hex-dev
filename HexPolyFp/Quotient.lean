/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Enumeration

public section

/-!
Project-side quotient API for `F_p[X] / (g)`.

The executable representation keeps canonical representatives reduced by the
existing `FpPoly.modByMonic` path.  The API is intentionally small: it exposes
the quotient operations needed by Rabin-style finite-field arguments while
leaving the deepest irreducible-gcd fact as a narrow helper theorem.
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
    simpa [zero, reduce_val_eq_mod, hval] using
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

/-! ## Quotient-coefficient polynomial evaluation -/

namespace Internal

/--
Evaluate a low-to-high quotient-coefficient list at a quotient point.

The list `[c₀, c₁, ...]` denotes `c₀ + β * (c₁ + β * (...))`. This
proof-facing evaluator is used by quotient-field root-count arguments where
the coefficients already live in `F_p[X] / (g)`.
-/
@[expose]
def evalCoeffList :
    List (Quotient g hmonic hg_pos) →
      Quotient g hmonic hg_pos → Quotient g hmonic hg_pos
  | [], _ => 0
  | c :: cs, β => c + β * evalCoeffList cs β

/-- Evaluating the empty quotient-coefficient list gives zero. -/
@[simp, grind =] theorem evalCoeffList_nil (β : Quotient g hmonic hg_pos) :
    evalCoeffList ([] : List (Quotient g hmonic hg_pos)) β = 0 :=
  rfl

/-- Evaluating a nonempty quotient-coefficient list unfolds one Horner step. -/
@[simp, grind =] theorem evalCoeffList_cons
    (c : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    (β : Quotient g hmonic hg_pos) :
    evalCoeffList (c :: cs) β = c + β * evalCoeffList cs β :=
  rfl

/--
Synthetic quotient coefficients for the divided difference of `cs` at the
base point `α`.

If `P` is represented by `cs`, this list represents the quotient
`(P(T) - P(α)) / (T - α)`. Its length is one less than the input list, which
is the measure used by root-count induction.
-/
@[expose]
def dividedDifferenceCoeffs :
    List (Quotient g hmonic hg_pos) →
      Quotient g hmonic hg_pos → List (Quotient g hmonic hg_pos)
  | [], _ => []
  | [_], _ => []
  | _ :: c :: cs, α =>
      evalCoeffList (c :: cs) α :: dividedDifferenceCoeffs (c :: cs) α

/-- The divided-difference coefficient list of the empty list is empty. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_nil (α : Quotient g hmonic hg_pos) :
    dividedDifferenceCoeffs ([] : List (Quotient g hmonic hg_pos)) α = [] :=
  rfl

/-- A constant polynomial has empty divided-difference coefficient list. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_singleton
    (c : Quotient g hmonic hg_pos) (α : Quotient g hmonic hg_pos) :
    dividedDifferenceCoeffs ([c] : List (Quotient g hmonic hg_pos)) α = [] :=
  rfl

/-- The divided-difference coefficient recursion peels the constant term and
evaluates the remaining tail at the base point. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_cons_cons
    (c d : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    (α : Quotient g hmonic hg_pos) :
    dividedDifferenceCoeffs (c :: d :: cs) α =
      evalCoeffList (d :: cs) α :: dividedDifferenceCoeffs (d :: cs) α :=
  rfl

/-- The synthetic divided-difference coefficient list has one fewer entry. -/
@[simp, grind =] theorem dividedDifferenceCoeffs_length
    (cs : List (Quotient g hmonic hg_pos)) (α : Quotient g hmonic hg_pos) :
    (dividedDifferenceCoeffs cs α).length = cs.length - 1 := by
  induction cs with
  | nil =>
      rfl
  | cons c cs ih =>
      cases cs with
      | nil =>
          rfl
      | cons d ds =>
          simp [dividedDifferenceCoeffs, ih]

/-- The synthetic divided-difference coefficient list is strictly shorter for
nonempty input. -/
theorem dividedDifferenceCoeffs_length_lt_of_ne_nil
    {cs : List (Quotient g hmonic hg_pos)} (hcs : cs ≠ [])
    (α : Quotient g hmonic hg_pos) :
    (dividedDifferenceCoeffs cs α).length < cs.length := by
  cases cs with
  | nil =>
      exact False.elim (hcs rfl)
  | cons c cs =>
      rw [dividedDifferenceCoeffs_length]
      exact Nat.sub_one_lt (Nat.succ_ne_zero cs.length)

/--
Evaluate the divided difference of a quotient-coefficient polynomial between
the base point `α` and target point `β`.
-/
@[expose]
def dividedDifference
    (cs : List (Quotient g hmonic hg_pos))
    (α β : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  evalCoeffList (dividedDifferenceCoeffs cs α) β

/-- The divided difference of the empty coefficient list is zero. -/
@[simp, grind =] theorem dividedDifference_nil
    (α β : Quotient g hmonic hg_pos) :
    dividedDifference ([] : List (Quotient g hmonic hg_pos)) α β = 0 :=
  rfl

/-- A nonconstant divided difference unfolds as a Horner step over the
synthetic coefficient tail. -/
@[simp, grind =] theorem dividedDifference_cons
    (c d : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    (α β : Quotient g hmonic hg_pos) :
    dividedDifference (c :: d :: cs) α β =
      evalCoeffList (d :: cs) α + β * dividedDifference (d :: cs) α β :=
  rfl

/--
The quotient-coefficient divided difference satisfies the usual identity
`P(β) - P(α) = (β - α) * DD(P, α, β)`.
-/
theorem evalCoeffList_sub_evalCoeffList_eq_sub_mul_dividedDifference
    (cs : List (Quotient g hmonic hg_pos))
    (α β : Quotient g hmonic hg_pos) :
    evalCoeffList cs β - evalCoeffList cs α =
      (β - α) * dividedDifference cs α β := by
  induction cs with
  | nil =>
      simp [dividedDifference]
  | cons c cs ih =>
      cases cs with
      | nil =>
          simp [dividedDifference, dividedDifferenceCoeffs]
      | cons d ds =>
          let Eβ := evalCoeffList (d :: ds) β
          let Eα := evalCoeffList (d :: ds) α
          let D := dividedDifference (d :: ds) α β
          let A := (β - α) * Eα
          let B := α * Eα
          let C := β * ((β - α) * D)
          have htail : Eβ - Eα = (β - α) * D := ih
          have hEβ : Eβ = (β - α) * D + Eα := by
            calc
              Eβ = (Eβ - Eα) + Eα := (sub_add_cancel Eβ Eα).symm
              _ = (β - α) * D + Eα := by rw [htail]
          apply add_right_cancel
            (evalCoeffList (c :: d :: ds) α)
            (evalCoeffList (c :: d :: ds) β - evalCoeffList (c :: d :: ds) α)
            ((β - α) * dividedDifference (c :: d :: ds) α β)
          calc
            (evalCoeffList (c :: d :: ds) β -
                  evalCoeffList (c :: d :: ds) α) +
                evalCoeffList (c :: d :: ds) α =
                evalCoeffList (c :: d :: ds) β := by
                  rw [sub_add_cancel]
            _ = c + β * Eβ := rfl
            _ = c + β * ((β - α) * D + Eα) := by rw [hEβ]
            _ = c + (β * ((β - α) * D) + β * Eα) := by rw [left_distrib]
            _ = c + (β * Eα + β * ((β - α) * D)) := by
                  rw [add_comm (β * ((β - α) * D)) (β * Eα)]
            _ = c + (((β - α) + α) * Eα + β * ((β - α) * D)) := by
                  rw [sub_add_cancel]
            _ = c + (((β - α) * Eα + α * Eα) + β * ((β - α) * D)) := by
                  rw [right_distrib]
            _ = ((β - α) * Eα + β * ((β - α) * D)) + (c + α * Eα) := by
                  change c + ((A + B) + C) = (A + C) + (c + B)
                  calc
                    c + ((A + B) + C) = c + (A + (B + C)) := by
                      rw [add_assoc]
                    _ = c + (A + (C + B)) := by
                      rw [add_comm B C]
                    _ = c + ((A + C) + B) := by
                      rw [← add_assoc A C B]
                    _ = (c + (A + C)) + B := by
                      rw [← add_assoc c (A + C) B]
                    _ = ((A + C) + c) + B := by
                      rw [add_comm c (A + C)]
                    _ = (A + C) + (c + B) := by
                      rw [add_assoc]
            _ = ((β - α) * Eα + (β * (β - α)) * D) + (c + α * Eα) := by
                  rw [mul_assoc]
            _ = ((β - α) * Eα + ((β - α) * β) * D) + (c + α * Eα) := by
                  rw [mul_comm β (β - α)]
            _ = ((β - α) * Eα + (β - α) * (β * D)) + (c + α * Eα) := by
                  rw [mul_assoc]
            _ = (β - α) * (Eα + β * D) + (c + α * Eα) := by
                  rw [left_distrib]
            _ = (β - α) * dividedDifference (c :: d :: ds) α β +
                  evalCoeffList (c :: d :: ds) α := rfl

private theorem zmod64_one_ne_zero :
    (1 : ZMod64 p) ≠ 0 := by
  intro hone
  have hnat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat hone
  have hp_two : 2 ≤ p :=
    (Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p)))
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at hnat
  exact absurd hnat (by omega)

/--
Evaluate an `FpPoly` at a quotient element by Horner iteration in the quotient.

The coefficients are embedded as constant quotient classes. This is a
project-side evaluation layer for root-counting arguments over
`F_p[X] / (g)`, without introducing a ring typeclass for the executable
quotient representation.
-/
@[expose]
def eval (f : FpPoly p) (β : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  f.toArray.toList.reverse.foldl
    (fun acc coeff =>
      acc * β + reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C coeff))
    0

/-- Stored `FpPoly` coefficients embedded as quotient constants, in low-to-high
coefficient order. -/
@[expose]
def evalQuotientCoeffs (f : FpPoly p) : List (Quotient g hmonic hg_pos) :=
  f.toArray.toList.map
    (fun coeff =>
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C coeff))

/-- Evaluating the zero polynomial in the quotient gives zero. -/
@[simp, grind =] theorem eval_zero (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (0 : FpPoly p) β = 0 := by
  rfl

/-- Evaluating a constant polynomial gives the corresponding constant quotient
class. -/
@[simp, grind =] theorem eval_C (c : ZMod64 p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) := by
  by_cases hc : c = 0
  · subst c
    change eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (0 : ZMod64 p)) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (0 : ZMod64 p))
    unfold eval DensePoly.toArray
    rw [show (DensePoly.C (0 : ZMod64 p)).coeffs = #[] by
      exact DensePoly.coeffs_C_zero]
    rfl
  · simp [eval, DensePoly.toArray, DensePoly.coeffs_C_of_ne_zero hc]

/-- Evaluating the polynomial indeterminate gives the input quotient element. -/
@[simp, grind =] theorem eval_X (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (FpPoly.X (p := p)) β = β := by
  change eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (DensePoly.monomial 1 (1 : ZMod64 p)) β = β
  unfold eval DensePoly.toArray DensePoly.monomial
  split
  · exact False.elim (zmod64_one_ne_zero ‹(1 : ZMod64 p) = 0›)
  · have hC1 : reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (1 : ZMod64 p)) = (1 : Quotient g hmonic hg_pos) := rfl
    have hC0_poly : (DensePoly.C (0 : ZMod64 p) : FpPoly p) = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_C, DensePoly.coeff_zero]
      split <;> rfl
    have hC0 : reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (0 : ZMod64 p)) = (0 : Quotient g hmonic hg_pos) := by
      rw [hC0_poly]
      rfl
    simp [Array.replicate, hC1]
    have hC0z : reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (Zero.zero : ZMod64 p)) = (0 : Quotient g hmonic hg_pos) := hC0
    rw [hC0z, add_zero]

private theorem reduce_C_zero :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (0 : ZMod64 p)) =
      (0 : Quotient g hmonic hg_pos) := by
  have hC0_poly : (DensePoly.C (0 : ZMod64 p) : FpPoly p) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_C, DensePoly.coeff_zero]
    split <;> rfl
  rw [hC0_poly]
  rfl

/-- Horner-folding the evaluation step over `n` zero coefficients scales the
accumulator by `β ^ n`. -/
private theorem foldl_eval_replicate_zero (β : Quotient g hmonic hg_pos) :
    ∀ n (acc : Quotient g hmonic hg_pos),
      (List.replicate n (0 : ZMod64 p)).foldl
          (fun acc coeff =>
            acc * β +
              reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.C coeff))
          acc =
        acc * β ^ n
  | 0, acc => by
      simp
  | n + 1, acc => by
      simp only [List.replicate_succ, List.foldl_cons]
      rw [reduce_C_zero, add_zero, foldl_eval_replicate_zero β n (acc * β)]
      calc
        (acc * β) * β ^ n = acc * (β * β ^ n) := by rw [mul_assoc]
        _ = acc * (β ^ n * β) := by rw [mul_comm β (β ^ n)]
        _ = acc * β ^ (n + 1) := by rfl

/-- Power-sum evaluation of a low-to-high coefficient list in the quotient,
starting exponents at `base`. -/
private def evalCoeffPowerSumFrom :
    List (ZMod64 p) → Nat → Quotient g hmonic hg_pos → Quotient g hmonic hg_pos
  | [], _, _ => 0
  | coeff :: coeffs, base, β =>
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C coeff) *
          β ^ base +
        evalCoeffPowerSumFrom coeffs (base + 1) β

/-- Recursive low-to-high scalar-coefficient evaluation, equivalent to Horner
but oriented by stored coefficient order. -/
private def evalScalarCoeffList :
    List (ZMod64 p) → Quotient g hmonic hg_pos → Quotient g hmonic hg_pos
  | [], _ => 0
  | coeff :: coeffs, β =>
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C coeff) +
        β * evalScalarCoeffList coeffs β

/-- `β * evalCoeffPowerSumFrom coeffs base β` equals the same power sum with its
starting exponent shifted from `base` to `base + 1`. -/
private theorem mul_evalCoeffPowerSumFrom_eq_succ
    (β : Quotient g hmonic hg_pos) :
    ∀ coeffs base,
      β * evalCoeffPowerSumFrom
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs base β =
        evalCoeffPowerSumFrom
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs (base + 1) β
  | [], _ => by
      simp [evalCoeffPowerSumFrom]
  | coeff :: coeffs, base => by
      simp only [evalCoeffPowerSumFrom]
      rw [left_distrib, mul_evalCoeffPowerSumFrom_eq_succ β coeffs (base + 1)]
      congr 1
      calc
        β *
            (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                  (DensePoly.C coeff) *
                β ^ base) =
            (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                  (DensePoly.C coeff) *
                β ^ base) *
              β := by rw [mul_comm]
        _ =
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.C coeff) *
              (β ^ base * β) := by rw [mul_assoc]
        _ =
            reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.C coeff) *
              β ^ (base + 1) := by rfl

/-- `evalScalarCoeffList coeffs β` equals `evalCoeffPowerSumFrom coeffs 0 β`,
the power sum started at exponent zero. -/
private theorem evalScalarCoeffList_eq_powerSumFrom_zero
    (β : Quotient g hmonic hg_pos) :
    ∀ coeffs,
      evalScalarCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs β =
        evalCoeffPowerSumFrom
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs 0 β
  | [] => by
      simp [evalScalarCoeffList, evalCoeffPowerSumFrom]
  | coeff :: coeffs => by
      simp only [evalScalarCoeffList, evalCoeffPowerSumFrom]
      rw [evalScalarCoeffList_eq_powerSumFrom_zero β coeffs]
      rw [mul_evalCoeffPowerSumFrom_eq_succ
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β coeffs 0]
      rw [pow_zero, mul_one]

/-- The Horner left-fold over the reversed coefficient list, started at zero,
equals `evalScalarCoeffList coeffs β` on the original order. -/
private theorem foldl_eval_reverse_eq_evalScalarCoeffList
    (β : Quotient g hmonic hg_pos) :
    ∀ coeffs,
      coeffs.reverse.foldl
          (fun acc coeff =>
            acc * β +
              reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.C coeff))
          0 =
        evalScalarCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs β
  | [] => by
      simp [evalScalarCoeffList]
  | coeff :: coeffs => by
      rw [List.reverse_cons, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [foldl_eval_reverse_eq_evalScalarCoeffList β coeffs]
      simp only [evalScalarCoeffList]
      rw [mul_comm (evalScalarCoeffList
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) coeffs β) β]
      rw [add_comm]

/-- `evalCoeffList` of the per-coefficient `reduce (DensePoly.C ·)` list equals
`evalScalarCoeffList coeffs β` on the raw scalar coefficients. -/
private theorem evalCoeffList_map_reduce_C_eq_evalScalarCoeffList
    (β : Quotient g hmonic hg_pos) :
    ∀ coeffs,
      evalCoeffList
          (coeffs.map
            (fun coeff =>
              reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                (DensePoly.C coeff)))
          β =
        evalScalarCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeffs β
  | [] => by
      rfl
  | coeff :: coeffs => by
      simp only [List.map_cons, evalCoeffList_cons, evalScalarCoeffList]
      rw [evalCoeffList_map_reduce_C_eq_evalScalarCoeffList β coeffs]

/-- Quotient evaluation of an `FpPoly` agrees with the proof-facing
quotient-coefficient evaluator on the embedded stored coefficient list. -/
theorem eval_eq_evalCoeffList (f : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β =
      evalCoeffList
        (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) β := by
  unfold eval evalQuotientCoeffs
  rw [foldl_eval_reverse_eq_evalScalarCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β f.toArray.toList]
  exact (evalCoeffList_map_reduce_C_eq_evalScalarCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β f.toArray.toList).symm

/-- `FpPoly`-specific divided-difference quotient evaluated between `α` and
`β`, using the existing executable coefficient representation. -/
@[expose]
def evalDividedDifference (f : FpPoly p)
    (α β : Quotient g hmonic hg_pos) : Quotient g hmonic hg_pos :=
  dividedDifference
    (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) α β

/-- Synthetic quotient coefficients for the `FpPoly` divided difference at
`α`. -/
@[expose]
def evalDividedDifferenceCoeffs (f : FpPoly p)
    (α : Quotient g hmonic hg_pos) : List (Quotient g hmonic hg_pos) :=
  dividedDifferenceCoeffs
    (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) α

/-- Evaluating the executable divided difference is the quotient-coefficient
evaluator applied to its synthetic coefficient list. -/
@[simp, grind =] theorem evalDividedDifference_eq_evalCoeffList
    (f : FpPoly p) (α β : Quotient g hmonic hg_pos) :
    evalDividedDifference (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        f α β =
      evalCoeffList
        (evalDividedDifferenceCoeffs
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α) β := by
  rfl

/-- The executable divided-difference coefficient list has one fewer entry
than the embedded coefficient list. -/
@[simp, grind =] theorem evalDividedDifferenceCoeffs_length
    (f : FpPoly p) (α : Quotient g hmonic hg_pos) :
    (evalDividedDifferenceCoeffs
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α).length =
      (evalQuotientCoeffs
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).length - 1 := by
  simp [evalDividedDifferenceCoeffs]

/-- The executable divided-difference coefficient list is strictly shorter
whenever the embedded input coefficient list is nonempty. -/
theorem evalDividedDifferenceCoeffs_length_lt_of_coeffs_ne_nil
    (f : FpPoly p)
    (hcoeffs :
      evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f ≠ [])
    (α : Quotient g hmonic hg_pos) :
    (evalDividedDifferenceCoeffs
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α).length <
      (evalQuotientCoeffs
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).length := by
  exact dividedDifferenceCoeffs_length_lt_of_ne_nil
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hcoeffs α

/-- `FpPoly` quotient evaluation satisfies the divided-difference identity. -/
theorem eval_sub_eval_eq_sub_mul_evalDividedDifference
    (f : FpPoly p) (α β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β -
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α =
      (β - α) *
        evalDividedDifference (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          f α β := by
  rw [eval_eq_evalCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β]
  rw [eval_eq_evalCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α]
  exact evalCoeffList_sub_evalCoeffList_eq_sub_mul_dividedDifference
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) α β

/-- If `α` is a quotient root of `f`, every value of `f` factors by
`β - α` through the executable-coefficient divided difference. -/
theorem eval_eq_sub_mul_evalDividedDifference_of_eval_eq_zero
    (f : FpPoly p) (α : Quotient g hmonic hg_pos)
    (hα : eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α = 0)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β =
      (β - α) *
        evalDividedDifference (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          f α β := by
  have h := eval_sub_eval_eq_sub_mul_evalDividedDifference
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f α β
  rw [hα, sub_zero] at h
  exact h

/-- `eval f β` equals `evalCoeffPowerSumFrom` over `f`'s stored coefficient list
started at exponent zero. -/
private theorem eval_eq_coeff_power_sum (f : FpPoly p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β =
      evalCoeffPowerSumFrom
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        f.toArray.toList 0 β := by
  unfold eval
  rw [foldl_eval_reverse_eq_evalScalarCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β f.toArray.toList]
  exact evalScalarCoeffList_eq_powerSumFrom_zero
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β f.toArray.toList

omit [ZMod64.PrimeModulus p] in
/-- Default-indexing `f`'s stored coefficient list returns the coefficient
`f.coeff n`. -/
private theorem eval_coeff_list_getD_eq_coeff (f : FpPoly p) (n : Nat) :
    f.toArray.toList.getD n (0 : ZMod64 p) = f.coeff n := by
  unfold DensePoly.toArray DensePoly.coeff
  rw [Array.getD_eq_getD_getElem?]
  change f.coeffs.toList[n]?.getD (0 : ZMod64 p) =
    f.coeffs[n]?.getD (Zero.zero : ZMod64 p)
  rw [Array.getElem?_toList]
  rfl

omit [ZMod64.PrimeModulus p] in
/-- Default-indexing `(List.range bound).map coeff` at `n` returns `coeff n` when
`n < bound` and `0` otherwise. -/
private theorem list_getD_map_range_zmod (bound n : Nat) (coeff : Nat → ZMod64 p) :
    ((List.range bound).map coeff).getD n (0 : ZMod64 p) =
      if n < bound then coeff n else 0 := by
  by_cases hn : n < bound
  · simp [hn, List.getD]
  · simp [hn, List.getD]

omit [ZMod64.PrimeModulus p] in
/-- Two `ZMod64 p` lists of equal length that agree at every default-indexed
position are equal. -/
private theorem list_eq_of_length_eq_of_getD_eq
    {xs ys : List (ZMod64 p)}
    (hlen : xs.length = ys.length)
    (hget : ∀ i, i < xs.length → xs.getD i 0 = ys.getD i 0) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hhead : x = y := by
            have h := hget 0 (by simp)
            simpa using h
          have hlen_tail : xs.length = ys.length := Nat.succ.inj hlen
          have htail : xs = ys := by
            apply ih hlen_tail
            intro i hi
            have h := hget (i + 1) (by simp [hi])
            simpa using h
          rw [hhead, htail]

omit [ZMod64.PrimeModulus p] in
/-- `f`'s stored coefficient list equals `(List.range f.size).map f.coeff`. -/
private theorem toArray_toList_eq_coeff_range (f : FpPoly p) :
    f.toArray.toList = (List.range f.size).map (fun i => f.coeff i) := by
  apply list_eq_of_length_eq_of_getD_eq
  · simp [DensePoly.toArray, DensePoly.size]
  · intro i hi
    have hi_size : i < f.size := by
      simpa [DensePoly.toArray, DensePoly.size] using hi
    rw [eval_coeff_list_getD_eq_coeff, list_getD_map_range_zmod]
    simp [hi_size]

/-- Power-sum evaluation of a coefficient function over a finite interval. -/
private def evalCoeffPowerSumUpTo
    (coeff : Nat → ZMod64 p) :
    Nat → Nat → Quotient g hmonic hg_pos → Quotient g hmonic hg_pos
  | 0, _, _ => 0
  | n + 1, base, β =>
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C (coeff base)) *
          β ^ base +
        evalCoeffPowerSumUpTo coeff n (base + 1) β

private theorem evalCoeffPowerSumFrom_range_eq_upTo
    (coeff : Nat → ZMod64 p) (β : Quotient g hmonic hg_pos) :
    ∀ n base,
      evalCoeffPowerSumFrom
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          ((List.range n).map (fun i => coeff (base + i))) base β =
        evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeff n base β
  | 0, base => by
      simp [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
  | n + 1, base => by
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map]
      simp only [evalCoeffPowerSumFrom, evalCoeffPowerSumUpTo]
      congr 1
      simpa [Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using evalCoeffPowerSumFrom_range_eq_upTo coeff β n (base + 1)

private theorem eval_eq_coeff_power_sum_upTo_size (f : FpPoly p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β =
      evalCoeffPowerSumUpTo
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (fun i => f.coeff i) f.size 0 β := by
  rw [eval_eq_coeff_power_sum, toArray_toList_eq_coeff_range]
  simpa using evalCoeffPowerSumFrom_range_eq_upTo
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (fun i => f.coeff i) β f.size 0

private theorem evalCoeffPowerSumUpTo_extend_zero
    (coeff : Nat → ZMod64 p) (β : Quotient g hmonic hg_pos)
    (hzero : ∀ i, bound ≤ i → coeff i = 0) :
    ∀ extra base,
      bound ≤ base →
        evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            coeff extra base β = 0
  | 0, base, _ => by
      simp [evalCoeffPowerSumUpTo]
  | extra + 1, base, hbase => by
      simp only [evalCoeffPowerSumUpTo]
      rw [hzero base hbase, reduce_C_zero, zero_mul,
        evalCoeffPowerSumUpTo_extend_zero coeff β hzero extra (base + 1) (by omega), zero_add]

private theorem evalCoeffPowerSumUpTo_succ_of_next_zero
    (coeff : Nat → ZMod64 p) (β : Quotient g hmonic hg_pos) :
    ∀ n base,
      coeff (base + n) = 0 →
        evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            coeff n base β =
          evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            coeff (n + 1) base β
  | 0, base, hzero => by
      have hz : coeff base = 0 := by simpa using hzero
      rw [evalCoeffPowerSumUpTo, evalCoeffPowerSumUpTo, hz, reduce_C_zero, zero_mul]
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base, hzero => by
      simp only [evalCoeffPowerSumUpTo]
      rw [evalCoeffPowerSumUpTo_succ_of_next_zero coeff β n (base + 1) (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hzero)]
      simp only [evalCoeffPowerSumUpTo]

/-- `evalCoeffPowerSumUpTo` is unchanged by extending its bound past the point
where the coefficients vanish, here from the offset `base`. -/
private theorem evalCoeffPowerSumUpTo_le_extend_base
    (coeff : Nat → ZMod64 p) (β : Quotient g hmonic hg_pos)
    (hzero : ∀ i, base + bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeff bound base β =
        evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeff (bound + extra) base β
  | 0 => by
      simp
  | extra + 1 => by
      rw [evalCoeffPowerSumUpTo_le_extend_base coeff β hzero extra, Nat.add_succ]
      exact evalCoeffPowerSumUpTo_succ_of_next_zero
        coeff β (bound + extra) base (hzero (base + (bound + extra)) (by omega))

/-- `evalCoeffPowerSumUpTo` from offset `0` is unchanged by extending its bound
past the point where the coefficients vanish. -/
private theorem evalCoeffPowerSumUpTo_le_extend
    (coeff : Nat → ZMod64 p) (β : Quotient g hmonic hg_pos)
    (hzero : ∀ i, bound ≤ i → coeff i = 0) :
    ∀ extra,
      evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeff bound 0 β =
        evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          coeff (bound + extra) 0 β := by
  intro extra
  exact evalCoeffPowerSumUpTo_le_extend_base
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    coeff β (base := 0) (bound := bound) (by simpa using hzero) extra

/-- `eval f β` equals the running power-sum of `f`'s coefficients taken up to
any `bound` at least as large as `f.size`. -/
private theorem eval_eq_coeff_power_sum_upTo_bound (f : FpPoly p)
    (β : Quotient g hmonic hg_pos) {bound : Nat} (hbound : f.size ≤ bound) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β =
      evalCoeffPowerSumUpTo
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (fun i => f.coeff i) bound 0 β := by
  rw [eval_eq_coeff_power_sum_upTo_size]
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hbound
  exact evalCoeffPowerSumUpTo_le_extend
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (fun i => f.coeff i) β
    (fun i hi => DensePoly.coeff_eq_zero_of_size_le f hi) extra

omit [ZMod64.PrimeModulus p] in
/-- `DensePoly.C` of a sum is the sum of the constant embeddings. -/
private theorem C_add_eq (a b : ZMod64 p) :
    (DensePoly.C (a + b) : FpPoly p) = DensePoly.C a + DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_add_semiring,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      show (0 : ZMod64 p) = 0 + 0
      grind

omit [ZMod64.PrimeModulus p] in
/-- `DensePoly.C` of a difference is the difference of the constant
embeddings. -/
private theorem C_sub_eq (a b : ZMod64 p) :
    (DensePoly.C (a - b) : FpPoly p) = DensePoly.C a - DensePoly.C b := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C, DensePoly.coeff_sub_ring,
    DensePoly.coeff_C, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      show (0 : ZMod64 p) = 0 - 0
      grind

omit [ZMod64.PrimeModulus p] in
/-- `DensePoly.C` of a product is the product of the constant embeddings. -/
private theorem C_mul_C_eq (a b : ZMod64 p) :
    (DensePoly.C (a * b) : FpPoly p) = DensePoly.C a * DensePoly.C b := by
  rw [FpPoly.C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  have hzero : a * (0 : ZMod64 p) = 0 := by grind
  rw [DensePoly.coeff_C, DensePoly.coeff_scale _ _ _ hzero, DensePoly.coeff_C]
  cases n with
  | zero => grind
  | succ n =>
      exact hzero.symm

/-- `reduce` of a constant polynomial keeps the constant as its representative,
since its degree lies below that of the modulus `g`. -/
private theorem reduce_C_val_eq (a : ZMod64 p) :
    (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C a)).val =
      (DensePoly.C a : FpPoly p) := by
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod]
  have hdeg : (DensePoly.C a : FpPoly p).degree?.getD 0 < g.degree?.getD 0 := by
    rw [DensePoly.degree?_C_getD]
    exact hg_pos
  exact DensePoly.mod_eq_self_of_degree_lt (DensePoly.C a : FpPoly p) g hdeg

/-- `reduce` of a constant sum splits as the sum of the reduced constants. -/
private theorem reduce_C_add (a b : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (a + b)) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C a) +
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C b) := by
  rw [C_add_eq]
  exact reduce_add (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (DensePoly.C a) (DensePoly.C b)

/-- `reduce` of a constant difference splits as the difference of the reduced
constants. -/
private theorem reduce_C_sub (a b : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (a - b)) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C a) -
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C b) := by
  apply ext
  rw [C_sub_eq, reduce_val, sub_val, reduce_C_val_eq, reduce_C_val_eq]

/-- `reduce` of a constant product splits as the product of the reduced
constants. -/
private theorem reduce_C_mul (a b : ZMod64 p) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C (a * b)) =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C a) *
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C b) := by
  rw [C_mul_C_eq]
  exact reduce_mul (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (DensePoly.C a) (DensePoly.C b)

/-- `evalCoeffPowerSumUpTo` is additive in its coefficient sequence: summing the
coefficients of `f` and `h` splits as the sum of the two power-sums. -/
private theorem evalCoeffPowerSumUpTo_add
    (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    ∀ n base,
      evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (fun i => f.coeff i + h.coeff i) n base β =
        evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (fun i => f.coeff i) n base β +
          evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (fun i => h.coeff i) n base β
  | 0, base => by
      simp [evalCoeffPowerSumUpTo]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [reduce_C_add, evalCoeffPowerSumUpTo_add f h β n (base + 1), right_distrib]
      exact add_pair_swap_quot _ _ _ _

private theorem neg_add_quot (a b : Quotient g hmonic hg_pos) :
    -(a + b) = -a + -b := by
  have hzero : (a + b) + (-a + -b) = 0 := by
    rw [add_pair_swap_quot a b (-a) (-b), add_right_neg, add_right_neg, zero_add]
  exact (eq_neg_of_add_eq_zero_right hzero).symm

private theorem add_sub_pair_swap
    (a b c d : Quotient g hmonic hg_pos) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  rw [sub_eq_add_neg a b, sub_eq_add_neg c d, sub_eq_add_neg (a + c) (b + d), neg_add_quot]
  exact add_pair_swap_quot a (-b) c (-d)

private theorem evalCoeffPowerSumUpTo_sub
    (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    ∀ n base,
      evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (fun i => f.coeff i - h.coeff i) n base β =
        evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (fun i => f.coeff i) n base β -
          evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (fun i => h.coeff i) n base β
  | 0, base => by
      simp [evalCoeffPowerSumUpTo, sub_self]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [reduce_C_sub, evalCoeffPowerSumUpTo_sub f h β n (base + 1), sub_mul]
      exact add_sub_pair_swap _ _ _ _

private theorem evalCoeffPowerSumUpTo_const_mul
    (c : ZMod64 p) (f : FpPoly p) (β : Quotient g hmonic hg_pos) :
    ∀ n base,
      evalCoeffPowerSumUpTo
          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (fun i => c * f.coeff i) n base β =
        reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (DensePoly.C c) *
          evalCoeffPowerSumUpTo
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
            (fun i => f.coeff i) n base β
  | 0, base => by
      simp [evalCoeffPowerSumUpTo, mul_zero]
  | n + 1, base => by
      simp only [evalCoeffPowerSumUpTo]
      rw [reduce_C_mul, evalCoeffPowerSumUpTo_const_mul c f β n (base + 1), left_distrib]
      congr 1
      rw [mul_assoc]

omit [ZMod64.PrimeModulus p] in
private theorem size_le_of_coeff_eq_zero_from_local (f : FpPoly p) (bound : Nat)
    (hzero : ∀ i, bound ≤ i → f.coeff i = 0) :
    f.size ≤ bound := by
  by_cases hle : f.size ≤ bound
  · exact hle
  · have hgt : bound < f.size := Nat.lt_of_not_ge hle
    have hpos : 0 < f.size := by omega
    have htop_zero : f.coeff (f.size - 1) = 0 := hzero (f.size - 1) (by omega)
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos htop_zero)

/-- Evaluation of a sum equals the sum of evaluations, proved by expanding both
sides as coefficient-power sums up to a common bound (`max f.size h.size`) and
applying additivity of the bounded power-sum evaluator. -/
private theorem eval_add_core_by_coeff_power_sum
    (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β +
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) β
    (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β
      (bound := bound) (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β
      (bound := bound) (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f + h).coeff i) =
          (fun i => f.coeff i + h.coeff i) := by
      funext i
      rw [DensePoly.coeff_add_semiring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_add
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β bound 0
  · change (f + h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from_local
    intro i hi
    rw [DensePoly.coeff_add_semiring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    show (0 : ZMod64 p) + 0 = 0
    grind

/-- Evaluation of a difference equals the difference of evaluations, proved by
expanding both sides as coefficient-power sums up to a common bound
(`max f.size h.size`) and applying subtractivity of the bounded power-sum
evaluator. -/
private theorem eval_sub_core_by_coeff_power_sum
    (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f - h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β -
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β := by
  let bound := max f.size h.size
  rw [eval_eq_coeff_power_sum_upTo_bound
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f - h) β
    (bound := bound)]
  · rw [eval_eq_coeff_power_sum_upTo_bound
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β
      (bound := bound) (Nat.le_max_left f.size h.size)]
    rw [eval_eq_coeff_power_sum_upTo_bound
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β
      (bound := bound) (Nat.le_max_right f.size h.size)]
    have hcoeff :
        (fun i => (f - h).coeff i) =
          (fun i => f.coeff i - h.coeff i) := by
      funext i
      rw [DensePoly.coeff_sub_ring]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_sub
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β bound 0
  · change (f - h).size ≤ max f.size h.size
    apply size_le_of_coeff_eq_zero_from_local
    intro i hi
    rw [DensePoly.coeff_sub_ring]
    rw [DensePoly.coeff_eq_zero_of_size_le f
        (Nat.le_trans (Nat.le_max_left f.size h.size) hi),
      DensePoly.coeff_eq_zero_of_size_le h
        (Nat.le_trans (Nat.le_max_right f.size h.size) hi)]
    show (0 : ZMod64 p) - 0 = 0
    grind

/-- Evaluation of a constant-scaled polynomial factors as the reduced constant
times the evaluation, proved by rewriting `C c * f` as a coefficient scaling and
applying the constant-multiple law of the bounded power-sum evaluator. -/
private theorem eval_C_mul_core_by_coeff_power_sum
    (c : ZMod64 p) (f : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C c * f) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β := by
  rw [FpPoly.C_mul_eq_scale]
  rw [eval_eq_coeff_power_sum_upTo_bound
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (DensePoly.scale c f) β (bound := f.size)]
  · rw [eval_eq_coeff_power_sum_upTo_size
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β]
    have hcoeff :
        (fun i => (DensePoly.scale c f).coeff i) =
          (fun i => c * f.coeff i) := by
      funext i
      have hzero : c * (0 : ZMod64 p) = 0 := by grind
      rw [DensePoly.coeff_scale _ _ _ hzero]
    rw [hcoeff]
    exact evalCoeffPowerSumUpTo_const_mul
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) c f β f.size 0
  · apply size_le_of_coeff_eq_zero_from_local
    intro i
    have hzero : c * (0 : ZMod64 p) = 0 := by grind
    rw [DensePoly.coeff_scale _ _ _ hzero]
    intro hi
    rw [DensePoly.coeff_eq_zero_of_size_le f hi]
    exact hzero

/-- Additivity of quotient evaluation, the private core re-exported as the public
`eval_add`; delegates to `eval_add_core_by_coeff_power_sum`. -/
private theorem eval_add_core (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β +
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β := by
  exact eval_add_core_by_coeff_power_sum
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β

/-- Subtractivity of quotient evaluation, the private core re-exported as the
public `eval_sub`; delegates to `eval_sub_core_by_coeff_power_sum`. -/
private theorem eval_sub_core (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f - h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β -
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β := by
  exact eval_sub_core_by_coeff_power_sum
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β

/-- Constant-factor law of quotient evaluation, the private core re-exported as
the public `eval_C_mul`; delegates to `eval_C_mul_core_by_coeff_power_sum`. -/
private theorem eval_C_mul_core (c : ZMod64 p) (f : FpPoly p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C c * f) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β := by
  exact eval_C_mul_core_by_coeff_power_sum
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) c f β

/-- Evaluating a monomial `monomial n c` yields the reduced constant `C c` times
the `n`-th power of the evaluation point; the zero-coefficient case collapses to
`0` and the nonzero case unfolds the dense representation and folds over the
trailing zeros. -/
private theorem eval_monomial_core (n : Nat) (c : ZMod64 p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial n c : FpPoly p) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        β ^ n := by
  by_cases hc : c = 0
  · subst c
    change eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial n (0 : ZMod64 p) : FpPoly p) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (DensePoly.C (0 : ZMod64 p)) *
        β ^ n
    unfold DensePoly.monomial
    rw [dif_pos (show (0 : ZMod64 p) = Zero.zero from rfl), eval_zero, reduce_C_zero, zero_mul]
  · unfold eval DensePoly.toArray DensePoly.monomial
    have hc0 : ¬ c = (Zero.zero : ZMod64 p) := hc
    rw [dif_neg hc0]
    simp only [Array.toList_push, Array.toList_replicate, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
      List.foldl_cons]
    rw [zero_mul, zero_add, List.reverse_replicate]
    exact foldl_eval_replicate_zero
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) β n
      (reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c))

/-- Evaluation into the quotient preserves polynomial addition. -/
theorem eval_add (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f + h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β +
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β :=
  eval_add_core (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β

/-- Evaluation into the quotient preserves polynomial subtraction. -/
theorem eval_sub (f h : FpPoly p) (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (f - h) β =
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β -
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) h β :=
  eval_sub_core (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f h β

/-- Pull a constant polynomial factor out of quotient evaluation. -/
theorem eval_C_mul (c : ZMod64 p) (f : FpPoly p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.C c * f) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β :=
  eval_C_mul_core (g := g) (hmonic := hmonic) (hg_pos := hg_pos) c f β

/-- Evaluating a monomial gives the embedded coefficient times the
corresponding power of the evaluation point. -/
theorem eval_monomial (n : Nat) (c : ZMod64 p)
    (β : Quotient g hmonic hg_pos) :
    eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (DensePoly.monomial n c : FpPoly p) β =
      reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) *
        β ^ n :=
  eval_monomial_core (g := g) (hmonic := hmonic) (hg_pos := hg_pos) n c β

/-- For a monic irreducible positive-degree modulus, the product of two nonzero
quotient elements is nonzero. -/
theorem mul_left_ne_zero_of_ne_zero (hg_irr : FpPoly.Irreducible g)
    {a b : Quotient g hmonic hg_pos} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  intro hab
  apply hb
  calc b
      = 1 * b := (one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel hg_irr ha]
    _ = a⁻¹ * (a * b) := mul_assoc _ _ _
    _ = a⁻¹ * 0 := by rw [hab]
    _ = 0 := mul_zero _

/-- Left multiplication by a nonzero quotient element is injective on the
quotient under an irreducible modulus. -/
theorem mul_left_injective (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0)
    {b₁ b₂ : Quotient g hmonic hg_pos} (heq : a * b₁ = a * b₂) :
    b₁ = b₂ := by
  have h := congrArg (fun x => a⁻¹ * x) heq
  dsimp at h
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel hg_irr ha, one_mul, one_mul] at h
  exact h

/-! ## Root counting over quotient coefficient lists -/

/--
The highest coefficient in a low-to-high quotient coefficient list is nonzero.

This predicate is the syntactic degree witness used by root-count induction:
such a list represents a nonzero quotient-coefficient polynomial of degree
`cs.length - 1`.
-/
@[expose]
def coeffListTopNonzero : List (Quotient g hmonic hg_pos) → Prop
  | cs => ∃ c, cs.getLast? = some c ∧ c ≠ 0

private theorem coeffListTopNonzero_tail_of_cons_cons
    {c d : Quotient g hmonic hg_pos} {cs : List (Quotient g hmonic hg_pos)}
    (h : coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs)) :
    coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (d :: cs) := by
  simpa [coeffListTopNonzero] using h

private theorem dividedDifferenceCoeffs_getLast?
    (c d : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    (α : Quotient g hmonic hg_pos) :
    (dividedDifferenceCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (c :: d :: cs) α).getLast? =
      (d :: cs).getLast? := by
  induction cs generalizing c d with
  | nil =>
      simp [dividedDifferenceCoeffs, evalCoeffList]
  | cons e es ih =>
      cases es with
      | nil =>
          simp [dividedDifferenceCoeffs, evalCoeffList]
      | cons q qs =>
          simpa [dividedDifferenceCoeffs] using ih e q

private theorem coeffListTopNonzero_dividedDifferenceCoeffs
    (c d : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    (α : Quotient g hmonic hg_pos)
    (h : coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (d :: cs)) :
    coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (dividedDifferenceCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (c :: d :: cs) α) := by
  rcases h with ⟨top, hlast, htop⟩
  refine ⟨top, ?_, htop⟩
  rw [dividedDifferenceCoeffs_getLast?]
  exact hlast

/-- Roots of a quotient-coefficient polynomial inside the canonical quotient
enumeration. -/
@[expose]
def rootsOfCoeffList (cs : List (Quotient g hmonic hg_pos)) :
    List (Quotient g hmonic hg_pos) :=
  (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
    (fun β => decide (evalCoeffList cs β = 0))

/-- Membership in `rootsOfCoeffList cs` is exactly vanishing of the
quotient-coefficient evaluator. -/
@[simp, grind =] theorem mem_rootsOfCoeffList
    (cs : List (Quotient g hmonic hg_pos)) (β : Quotient g hmonic hg_pos) :
    β ∈ rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs ↔
      evalCoeffList cs β = 0 := by
  simp [rootsOfCoeffList, mem_elements β]

/-- The quotient-coefficient root list has no duplicate roots. -/
theorem rootsOfCoeffList_nodup (cs : List (Quotient g hmonic hg_pos)) :
    (rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs).Nodup := by
  unfold rootsOfCoeffList
  exact (elements_nodup (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter _

private theorem length_filter_le (p : α → Bool) :
    ∀ xs : List α, (xs.filter p).length ≤ xs.length
  | [] => by simp
  | x :: xs => by
      by_cases hx : p x = true
      · rw [List.filter_cons_of_pos hx]
        simp only [List.length_cons]
        exact Nat.succ_le_succ (length_filter_le p xs)
      · rw [List.filter_cons_of_neg hx]
        exact Nat.le_trans (length_filter_le p xs) (Nat.le_succ xs.length)

private theorem length_le_of_nodup_subset
    {α : Type} [DecidableEq α] {xs ys : List α}
    (hxs : xs.Nodup) (hys : ys.Nodup)
    (hsub : ∀ a, a ∈ xs → a ∈ ys) :
    xs.length ≤ ys.length := by
  let zs := ys.filter (fun a => decide (a ∈ xs))
  have hzs_nodup : zs.Nodup := hys.filter _
  have hmem : ∀ a, a ∈ xs ↔ a ∈ zs := by
    intro a
    constructor
    · intro ha
      exact List.mem_filter.mpr ⟨hsub a ha, decide_eq_true ha⟩
    · intro ha
      exact of_decide_eq_true (List.mem_filter.mp ha).2
  have hperm : List.Perm xs zs :=
    perm_of_nodup_mem_iff hxs hzs_nodup hmem
  have hlen_eq : xs.length = zs.length := hperm.length_eq
  calc
    xs.length = zs.length := hlen_eq
    _ ≤ ys.length := length_filter_le (fun a => decide (a ∈ xs)) ys

private theorem roots_without_base_subset_dividedDifference_roots
    (hg_irr : FpPoly.Irreducible g)
    (c d : Quotient g hmonic hg_pos) (cs : List (Quotient g hmonic hg_pos))
    {α β : Quotient g hmonic hg_pos}
    (hα : α ∈ rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs))
    (hβ : β ∈ rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs))
    (hβα : β ≠ α) :
    β ∈ rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (dividedDifferenceCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (c :: d :: cs) α) := by
  have hα_eval :
      evalCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (c :: d :: cs) α = 0 :=
    (mem_rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs) α).mp hα
  have hβ_eval :
      evalCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (c :: d :: cs) β = 0 :=
    (mem_rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs) β).mp hβ
  have hident :=
    evalCoeffList_sub_evalCoeffList_eq_sub_mul_dividedDifference
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (c :: d :: cs) α β
  rw [hβ_eval, hα_eval] at hident
  have hzero_sub : (0 : Quotient g hmonic hg_pos) -
      (0 : Quotient g hmonic hg_pos) = 0 := by
    rw [sub_zero]
  rw [hzero_sub] at hident
  have hsub_ne : β - α ≠ 0 :=
    sub_ne_zero_of_ne (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hβα
  have hdd_zero :
      dividedDifference (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
        (c :: d :: cs) α β = 0 := by
    apply mul_left_injective hg_irr hsub_ne
    rw [mul_zero]
    exact hident.symm
  exact (mem_rootsOfCoeffList
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
    (dividedDifferenceCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (c :: d :: cs) α) β).mpr hdd_zero

/--
A nonzero quotient-coefficient polynomial has at most its degree many roots in
the duplicate-free quotient enumeration.

The coefficient list is low-to-high, and `coeffListTopNonzero cs` says the
highest listed coefficient is nonzero, so the degree bound is `cs.length - 1`.
-/
theorem rootsOfCoeffList_length_le_degree
    (hg_irr : FpPoly.Irreducible g)
    (cs : List (Quotient g hmonic hg_pos))
    (htop : coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs) :
    (rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs).length ≤
      cs.length - 1 := by
  have hmain :
      ∀ n, ∀ cs : List (Quotient g hmonic hg_pos), cs.length = n →
        coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs →
        (rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs).length ≤
          cs.length - 1 := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro cs hlen htop
        cases cs with
        | nil =>
            rcases htop with ⟨top, hlast, _htop_ne⟩
            simp at hlast
        | cons c cs =>
            cases cs with
            | nil =>
                rcases htop with ⟨top, hlast, htop_ne⟩
                simp at hlast
                subst top
                unfold rootsOfCoeffList
                simp [evalCoeffList, htop_ne]
            | cons d ds =>
                let P := c :: d :: ds
                let rootsP :=
                  rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos) P
                by_cases hnil : rootsP = []
                · rw [show rootsOfCoeffList (g := g) (hmonic := hmonic)
                      (hg_pos := hg_pos) P = [] from hnil]
                  simp
                · cases hrootsP : rootsP with
                  | nil =>
                      exact False.elim (hnil hrootsP)
                  | cons α rest =>
                      have hα : α ∈ rootsOfCoeffList
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) P := by
                        show α ∈ rootsP
                        rw [hrootsP]
                        exact List.mem_cons_self
                      let rootsWithoutα :=
                        rootsP.filter (fun β => decide (β ≠ α))
                      let ddCoeffs :=
                        dividedDifferenceCoeffs
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) P α
                      let rootsDD :=
                        rootsOfCoeffList
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) ddCoeffs
                      have hrootsP_nodup : rootsP.Nodup := by
                        dsimp [rootsP]
                        exact rootsOfCoeffList_nodup
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos) P
                      have hα_filter_len :
                          rootsWithoutα.length = rootsP.length - 1 := by
                        exact length_filter_ne_eq_pred_of_mem_nodup
                          (z := α) hα hrootsP_nodup
                      have hdd_top : coeffListTopNonzero
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                          ddCoeffs := by
                        dsimp [ddCoeffs, P]
                        exact coeffListTopNonzero_dividedDifferenceCoeffs
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                          c d ds α
                          (coeffListTopNonzero_tail_of_cons_cons
                            (g := g) (hmonic := hmonic) (hg_pos := hg_pos) htop)
                      have hsub :
                          ∀ β, β ∈ rootsWithoutα → β ∈ rootsDD := by
                        intro β hβ
                        have hβ_rootsP : β ∈ rootsP :=
                          (List.mem_filter.mp hβ).1
                        have hβ_ne : β ≠ α :=
                          of_decide_eq_true (List.mem_filter.mp hβ).2
                        dsimp [rootsDD, ddCoeffs, P]
                        exact roots_without_base_subset_dividedDifference_roots
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                          hg_irr c d ds hα hβ_rootsP hβ_ne
                      have hwithout_le_dd :
                          rootsWithoutα.length ≤ rootsDD.length := by
                        apply length_le_of_nodup_subset
                        · exact hrootsP_nodup.filter _
                        · dsimp [rootsDD]
                          exact rootsOfCoeffList_nodup
                            (g := g) (hmonic := hmonic) (hg_pos := hg_pos) ddCoeffs
                        · exact hsub
                      have hdd_len : ddCoeffs.length = P.length - 1 := by
                        dsimp [ddCoeffs, P]
                        exact dividedDifferenceCoeffs_length
                          (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
                          (c :: d :: ds) α
                      have hP_len : P.length = n := by
                        dsimp [P]
                        exact hlen
                      have hP_len_two : 2 ≤ P.length := by
                        dsimp [P]
                        simp
                      have hdd_lt : ddCoeffs.length < n := by
                        omega
                      have hdd_bound :
                          rootsDD.length ≤ ddCoeffs.length - 1 := by
                        dsimp [rootsDD]
                        exact ih ddCoeffs.length hdd_lt ddCoeffs rfl hdd_top
                      have hrootsP_pos : 0 < rootsP.length := by
                        rw [hrootsP]
                        simp
                      have hwithout_bound :
                          rootsWithoutα.length ≤ P.length - 2 := by
                        calc
                          rootsWithoutα.length ≤ rootsDD.length := hwithout_le_dd
                          _ ≤ ddCoeffs.length - 1 := hdd_bound
                          _ = P.length - 2 := by omega
                      have hrootsP_eq :
                          rootsP.length = rootsWithoutα.length + 1 := by
                        omega
                      have hrootsP_bound : rootsP.length ≤ P.length - 1 := by
                        omega
                      exact hrootsP_bound
  exact hmain cs.length cs rfl htop

/-- Direct root-count bound for the canonical `elements` filter form used by
callers. -/
theorem evalCoeffList_rootsIn_elements_length_le_degree
    (hg_irr : FpPoly.Irreducible g)
    (cs : List (Quotient g hmonic hg_pos))
    (htop : coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos) cs) :
    ((elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
      (fun β => decide (evalCoeffList cs β = 0))).length ≤ cs.length - 1 :=
  rootsOfCoeffList_length_le_degree
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr cs htop

private theorem evalQuotientCoeffs_length (f : FpPoly p) :
    (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).length =
      f.size := by
  simp [evalQuotientCoeffs, DensePoly.toArray, DensePoly.size]

omit [ZMod64.PrimeModulus p] in
private theorem fpPoly_eq_zero_of_size_eq_zero {f : FpPoly p} (hsize : f.size = 0) :
    f = 0 := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_eq_zero_of_size_le f (by omega : f.size ≤ n),
    DensePoly.coeff_zero]
  rfl

private theorem reduce_C_ne_zero_of_ne_zero {c : ZMod64 p} (hc : c ≠ 0) :
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C c) ≠
      (0 : Quotient g hmonic hg_pos) := by
  intro hzero
  have hval := congrArg Quotient.val hzero
  have hdeg : (DensePoly.C c : FpPoly p).degree?.getD 0 < g.degree?.getD 0 := by
    rw [DensePoly.degree?_C_getD]
    exact hg_pos
  rw [reduce_val, FpPoly.modByMonic, DensePoly.modByMonic_eq_mod,
    DensePoly.mod_eq_self_of_degree_lt (DensePoly.C c : FpPoly p) g hdeg,
    zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero] at hval
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hval
  change (DensePoly.C c : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  simp at hcoeff
  exact hc hcoeff

private theorem evalQuotientCoeffs_topNonzero_of_ne_zero
    (f : FpPoly p) (hf : f ≠ 0) :
    coeffListTopNonzero (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) := by
  have hsize_pos : 0 < f.size := by
    by_cases hsize : f.size = 0
    · exact False.elim (hf (fpPoly_eq_zero_of_size_eq_zero hsize))
    · omega
  let topCoeff := f.coeff (f.size - 1)
  let topQuot :=
    reduce (g := g) (hmonic := hmonic) (hg_pos := hg_pos) (DensePoly.C topCoeff)
  refine ⟨topQuot, ?_, ?_⟩
  · unfold evalQuotientCoeffs topQuot topCoeff DensePoly.toArray DensePoly.coeff
    rw [List.getLast?_map, List.getLast?_eq_getElem?, Array.getElem?_toList]
    rw [Array.getElem?_eq_getElem
      (by simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hsize_pos)]
    rw [Array.getElem_eq_getD (Zero.zero : ZMod64 p)]
    simp [DensePoly.size]
  · exact reduce_C_ne_zero_of_ne_zero
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      (DensePoly.coeff_last_ne_zero_of_pos_size f hsize_pos)

/-- Roots of an `FpPoly` quotient evaluation inside the canonical quotient
enumeration. -/
@[expose]
def rootsOfFpPoly (f : FpPoly p) : List (Quotient g hmonic hg_pos) :=
  (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
    (fun β => decide (eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β = 0))

/-- Membership in `rootsOfFpPoly f` is exactly vanishing of quotient
evaluation of `f`. -/
@[simp, grind =] theorem mem_rootsOfFpPoly
    (f : FpPoly p) (β : Quotient g hmonic hg_pos) :
    β ∈ rootsOfFpPoly (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f ↔
      eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β = 0 := by
  simp [rootsOfFpPoly, mem_elements β]

/-- The `FpPoly` quotient-evaluation root list has no duplicate roots. -/
theorem rootsOfFpPoly_nodup (f : FpPoly p) :
    (rootsOfFpPoly (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).Nodup := by
  unfold rootsOfFpPoly
  exact (elements_nodup (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter _

/--
A nonzero `FpPoly` has at most `f.size - 1` quotient roots in the
duplicate-free quotient enumeration, provided the modulus is irreducible.
-/
theorem rootsOfFpPoly_length_le_degree
    (hg_irr : FpPoly.Irreducible g)
    (f : FpPoly p) (hf : f ≠ 0) :
    (rootsOfFpPoly (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f).length ≤
      f.size - 1 := by
  have hcoeffs_top :=
    evalQuotientCoeffs_topNonzero_of_ne_zero
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f hf
  have hcoeff_bound :=
    rootsOfCoeffList_length_le_degree
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr
      (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f)
      hcoeffs_top
  have hroots_eq :
      rootsOfFpPoly (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f =
        rootsOfCoeffList (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
          (evalQuotientCoeffs (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f) := by
    unfold rootsOfFpPoly rootsOfCoeffList
    apply List.filter_congr
    intro β hβ
    rw [eval_eq_evalCoeffList
      (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β]
  rw [hroots_eq]
  rw [evalQuotientCoeffs_length
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f] at hcoeff_bound
  exact hcoeff_bound

/-- Direct root-count bound for the canonical `elements` filter form used by
callers evaluating an `FpPoly` in the quotient. -/
theorem eval_rootsIn_elements_length_le_degree
    (hg_irr : FpPoly.Irreducible g)
    (f : FpPoly p) (hf : f ≠ 0) :
    ((elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
      (fun β => decide
        (eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β = 0))).length ≤
      f.size - 1 := by
  exact rootsOfFpPoly_length_le_degree
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr f hf

/-- Multiplication by a nonzero quotient element permutes the nonzero
enumeration. The list of nonzero elements multiplied on the left by `a` is a
permutation of the original nonzero list. -/
theorem nonzeroElements_map_mul_left_perm (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    List.Perm
      ((nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).map
        (fun b => a * b))
      (nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)) := by
  let L : List (Quotient g hmonic hg_pos) :=
    nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
  have hL_nodup : L.Nodup :=
    nonzeroElements_nodup (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
  have hmap_inj :
      ∀ b₁, b₁ ∈ L → ∀ b₂, b₂ ∈ L →
        (fun b => a * b) b₁ = (fun b => a * b) b₂ → b₁ = b₂ := by
    intro b₁ _ b₂ _ heq
    exact mul_left_injective hg_irr ha heq
  have hmap_nodup : (L.map (fun b => a * b)).Nodup :=
    nodup_map_of_injective hL_nodup hmap_inj
  have hmem_iff : ∀ c, c ∈ L.map (fun b => a * b) ↔ c ∈ L := by
    intro c
    constructor
    · intro hc
      rcases List.mem_map.mp hc with ⟨b, hb_mem, hbc⟩
      have hb_ne : b ≠ 0 := (mem_nonzeroElements b).mp hb_mem
      have hab_ne : a * b ≠ 0 := mul_left_ne_zero_of_ne_zero hg_irr ha hb_ne
      have hc_ne : c ≠ 0 := hbc ▸ hab_ne
      exact (mem_nonzeroElements c).mpr hc_ne
    · intro hc
      have hc_ne : c ≠ 0 := (mem_nonzeroElements c).mp hc
      refine List.mem_map.mpr ⟨a⁻¹ * c, ?_, ?_⟩
      · apply (mem_nonzeroElements _).mpr
        intro hac
        apply hc_ne
        calc c
            = 1 * c := (one_mul c).symm
          _ = (a * a⁻¹) * c := by rw [mul_inv_cancel hg_irr ha]
          _ = a * (a⁻¹ * c) := mul_assoc _ _ _
          _ = a * 0 := by rw [hac]
          _ = 0 := mul_zero _
      · rw [← mul_assoc, mul_inv_cancel hg_irr ha, one_mul]
  exact perm_of_nodup_mem_iff hmap_nodup hL_nodup hmem_iff

private theorem fpPoly_one_ne_zero :
    (1 : FpPoly p) ≠ 0 := by
  intro hone
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hone
  change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
  simp only [if_true] at hcoeff
  exact zmod64_one_ne_zero hcoeff

/-- The quotient is nontrivial: `1` and `0` are distinct quotient elements
under a positive-degree modulus. -/
theorem one_ne_zero :
    (1 : Quotient g hmonic hg_pos) ≠ (0 : Quotient g hmonic hg_pos) := by
  intro h
  have hval := congrArg Quotient.val h
  rw [one_val_eq_one] at hval
  have hzero_val : (0 : Quotient g hmonic hg_pos).val = (0 : FpPoly p) := by
    letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
    rw [zero_val, FpPoly.modByMonic, DensePoly.modByMonic_zero]
  rw [hzero_val] at hval
  exact fpPoly_one_ne_zero hval

/-- Product of a list of quotient elements (right fold). -/
@[expose]
def listProd (xs : List (Quotient g hmonic hg_pos)) : Quotient g hmonic hg_pos :=
  xs.foldr (· * ·) 1

/-- The product of an empty quotient list is one. -/
@[simp, grind =] theorem listProd_nil :
    listProd ([] : List (Quotient g hmonic hg_pos)) = 1 :=
  rfl

/-- The product of a cons list multiplies the head by the product of the tail. -/
@[simp, grind =] theorem listProd_cons (x : Quotient g hmonic hg_pos)
    (xs : List (Quotient g hmonic hg_pos)) :
    listProd (x :: xs) = x * listProd xs :=
  rfl

/-- The product of an appended quotient list factors as the product of the two
pieces. -/
theorem listProd_append (xs ys : List (Quotient g hmonic hg_pos)) :
    listProd (xs ++ ys) = listProd xs * listProd ys := by
  induction xs with
  | nil =>
      simp [listProd_nil, one_mul]
  | cons x xs ih =>
      simp only [List.cons_append, listProd_cons, ih]
      rw [mul_assoc]

/-- The list product is invariant under `List.Perm`. -/
theorem listProd_perm {xs ys : List (Quotient g hmonic hg_pos)}
    (h : List.Perm xs ys) :
    listProd xs = listProd ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
      simp only [listProd_cons]
      rw [ih]
  | swap x y zs =>
      simp only [listProd_cons]
      rw [← mul_assoc, ← mul_assoc, mul_comm x y]
  | trans _ _ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- Mapping a list by left-multiplication factors out as a power of the
multiplier times the original list product. -/
theorem listProd_map_mul_left (a : Quotient g hmonic hg_pos)
    (xs : List (Quotient g hmonic hg_pos)) :
    listProd (xs.map (fun b => a * b)) = a ^ xs.length * listProd xs := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.length_nil, listProd_nil, pow_zero, one_mul]
  | cons x xs ih =>
      calc listProd ((x :: xs).map (fun b => a * b))
          = (a * x) * listProd (xs.map (fun b => a * b)) := by
              simp only [List.map_cons, listProd_cons]
        _ = (a * x) * (a ^ xs.length * listProd xs) := by rw [ih]
        _ = a * (x * (a ^ xs.length * listProd xs)) := mul_assoc ..
        _ = a * ((x * a ^ xs.length) * listProd xs) := by
              rw [mul_assoc x (a ^ xs.length) (listProd xs)]
        _ = a * ((a ^ xs.length * x) * listProd xs) := by
              rw [mul_comm x (a ^ xs.length)]
        _ = a * (a ^ xs.length * (x * listProd xs)) := by
              rw [mul_assoc (a ^ xs.length) x (listProd xs)]
        _ = (a * a ^ xs.length) * (x * listProd xs) := (mul_assoc ..).symm
        _ = a ^ (xs.length + 1) * (x * listProd xs) := by
              rw [pow_succ, mul_comm (a ^ xs.length) a]
        _ = a ^ (x :: xs).length * listProd (x :: xs) := by
              simp only [listProd_cons, List.length_cons]

/-- The product of a list of nonzero quotient elements is nonzero, under a
monic irreducible positive-degree modulus. -/
theorem listProd_ne_zero (hg_irr : FpPoly.Irreducible g)
    {xs : List (Quotient g hmonic hg_pos)}
    (hxs : ∀ x ∈ xs, x ≠ 0) :
    listProd xs ≠ 0 := by
  induction xs with
  | nil =>
      simp only [listProd_nil]
      exact one_ne_zero
  | cons x xs ih =>
      simp only [listProd_cons]
      apply mul_left_ne_zero_of_ne_zero hg_irr
      · exact hxs x List.mem_cons_self
      · exact ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))

/-- Finite-field exponent theorem for the quotient: every nonzero quotient
element raised to the cardinality of the nonzero group equals `1`. -/
theorem pow_pred_card_eq_one_of_ne_zero
    (hg_irr : FpPoly.Irreducible g)
    {a : Quotient g hmonic hg_pos} (ha : a ≠ 0) :
    a ^ (p ^ g.degree?.getD 0 - 1) = 1 := by
  let L : List (Quotient g hmonic hg_pos) :=
    nonzeroElements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
  let P : Quotient g hmonic hg_pos := listProd L
  have hL_card : L.length = p ^ g.degree?.getD 0 - 1 :=
    nonzeroElements_card (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
  have hP_ne : P ≠ 0 :=
    listProd_ne_zero hg_irr (fun x hx => (mem_nonzeroElements x).mp hx)
  have hperm := nonzeroElements_map_mul_left_perm
    (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr ha
  have hprod_eq : listProd (L.map (fun b => a * b)) = P :=
    listProd_perm hperm
  have hfactor : listProd (L.map (fun b => a * b)) = a ^ L.length * P :=
    listProd_map_mul_left a L
  have hkey : a ^ L.length * P = P := hfactor.symm.trans hprod_eq
  have hcancel : a ^ L.length * P * P⁻¹ = P * P⁻¹ :=
    congrArg (fun x => x * P⁻¹) hkey
  rw [mul_assoc, mul_inv_cancel hg_irr hP_ne, mul_one] at hcancel
  rw [hL_card] at hcancel
  exact hcancel

/-- Frobenius fixed-point theorem for the quotient: every element of the
finite-field quotient `F_p[X] / (g)` is fixed by raising to the cardinality
`p ^ deg(g)`. -/
theorem pow_card_eq_self_of_irreducible
    (hg_irr : FpPoly.Irreducible g) (a : Quotient g hmonic hg_pos) :
    a ^ (p ^ g.degree?.getD 0) = a := by
  have hp_two : 2 ≤ p :=
    Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
  have hpos : 0 < p ^ g.degree?.getD 0 := Nat.pow_pos (by omega)
  have hsplit : p ^ g.degree?.getD 0 = (p ^ g.degree?.getD 0 - 1) + 1 := by
    omega
  by_cases ha : a = 0
  · rw [ha, hsplit, pow_succ, mul_zero]
  · rw [hsplit, pow_succ, pow_pred_card_eq_one_of_ne_zero hg_irr ha, one_mul]

/-- Adding any multiple of the modulus degree to a Frobenius exponent does not
change the quotient Frobenius iterate. -/
theorem pow_pPow_add_mul_degree_eq
    (hg_irr : FpPoly.Irreducible g) (a : Quotient g hmonic hg_pos) (m q : Nat) :
    a ^ (p ^ (m + g.degree?.getD 0 * q)) = a ^ (p ^ m) := by
  induction q with
  | zero =>
      rw [Nat.mul_zero, Nat.add_zero]
  | succ q ih =>
      have hidx :
          m + g.degree?.getD 0 * (q + 1) =
            (m + g.degree?.getD 0 * q) + g.degree?.getD 0 := by
        rw [Nat.mul_succ]
        omega
      calc
        a ^ (p ^ (m + g.degree?.getD 0 * (q + 1)))
            = a ^ (p ^ ((m + g.degree?.getD 0 * q) + g.degree?.getD 0)) := by
              rw [hidx]
        _ = (a ^ (p ^ (m + g.degree?.getD 0 * q))) ^
              (p ^ g.degree?.getD 0) := by
              rw [Nat.pow_add, pow_mul]
        _ = (a ^ (p ^ m)) ^ (p ^ g.degree?.getD 0) := by rw [ih]
        _ = a ^ (p ^ m) := pow_card_eq_self_of_irreducible hg_irr _

/-- If a quotient element is fixed by the `n`th Frobenius iterate, then it is
fixed by the remainder of `n` modulo the modulus degree. -/
theorem pow_pPow_mod_degree_eq_of_fixed
    (hg_irr : FpPoly.Irreducible g) {a : Quotient g hmonic hg_pos} {n : Nat}
    (hfixed : a ^ (p ^ n) = a) :
    a ^ (p ^ (n % g.degree?.getD 0)) = a := by
  have hdecomp :
      n % g.degree?.getD 0 + g.degree?.getD 0 * (n / g.degree?.getD 0) = n :=
    Nat.mod_add_div n ((g.degree?).getD 0)
  have hperiod :
      a ^ (p ^ (n % g.degree?.getD 0 +
          g.degree?.getD 0 * (n / g.degree?.getD 0))) =
        a ^ (p ^ (n % g.degree?.getD 0)) :=
    pow_pPow_add_mul_degree_eq (g := g) (hmonic := hmonic) (hg_pos := hg_pos)
      hg_irr a (n % g.degree?.getD 0) (n / g.degree?.getD 0)
  rw [hdecomp] at hperiod
  rw [← hperiod]
  exact hfixed

omit [ZMod64.PrimeModulus p] in
private theorem size_le_of_coeff_eq_zero_from
    (f : FpPoly p) {bound : Nat}
    (hzero : ∀ i, bound ≤ i → f.coeff i = 0) :
    f.size ≤ bound := by
  by_cases hle : f.size ≤ bound
  · exact hle
  · have hlt : bound < f.size := Nat.lt_of_not_ge hle
    have hsize_pos : 0 < f.size := by omega
    have htop := DensePoly.coeff_last_ne_zero_of_pos_size f hsize_pos
    have hbound : bound ≤ f.size - 1 := by omega
    exact False.elim (htop (hzero (f.size - 1) hbound))

private theorem monomial_pPow_sub_X_ne_zero {r : Nat} (hr_pos : 0 < r) :
    (DensePoly.monomial (p ^ r) (1 : ZMod64 p) - FpPoly.X : FpPoly p) ≠ 0 := by
  intro hzero
  have hp_gt_one : 1 < p := by
    have hp_two : 2 ≤ p :=
      Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
    omega
  have hp_pow_gt_one : 1 < p ^ r := Nat.pow_lt_pow_right hp_gt_one hr_pos
  have hpow_ne_one : p ^ r ≠ 1 := by omega
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff (p ^ r)) hzero
  change
      (DensePoly.monomial (p ^ r) (1 : ZMod64 p) -
          DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p).coeff (p ^ r) =
        (0 : FpPoly p).coeff (p ^ r) at hcoeff
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial,
    DensePoly.coeff_monomial, DensePoly.coeff_zero] at hcoeff
  simp [hpow_ne_one] at hcoeff
  have hone_zero : (1 : ZMod64 p) = 0 := by
    calc
      (1 : ZMod64 p) = 1 - 0 := by grind
      _ = 0 := hcoeff
  exact zmod64_one_ne_zero hone_zero

private theorem monomial_pPow_sub_X_size_sub_one_le {r : Nat} (hr_pos : 0 < r) :
    (DensePoly.monomial (p ^ r) (1 : ZMod64 p) - FpPoly.X : FpPoly p).size - 1 ≤
      p ^ r := by
  have hp_gt_one : 1 < p := by
    have hp_two : 2 ≤ p :=
      Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
    omega
  have hp_pow_gt_one : 1 < p ^ r := Nat.pow_lt_pow_right hp_gt_one hr_pos
  have hsize_le :
      (DensePoly.monomial (p ^ r) (1 : ZMod64 p) - FpPoly.X : FpPoly p).size ≤
        p ^ r + 1 := by
    apply size_le_of_coeff_eq_zero_from
    intro i hi
    have hi_ne_pow : i ≠ p ^ r := by omega
    have hi_ne_one : i ≠ 1 := by omega
    change
        (DensePoly.monomial (p ^ r) (1 : ZMod64 p) -
            DensePoly.monomial 1 (1 : ZMod64 p) : FpPoly p).coeff i = 0
    rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial,
      DensePoly.coeff_monomial]
    simp [hi_ne_pow, hi_ne_one]
    grind
  omega

/--
If every element of the irreducible quotient is fixed by the `n`th Frobenius
iterate, then the modulus degree divides `n`.

This is the quotient-side order theorem used by Rabin soundness: a nonzero
remainder `r = n % deg(g)` would make every quotient element a root of
`T^(p^r) - T`, contradicting the root-count bound because the quotient has
`p^deg(g)` elements.
-/
theorem deg_dvd_of_pow_pPowN_eq_self_universal
    (hg_irr : FpPoly.Irreducible g) {n : Nat}
    (h : ∀ β : Quotient g hmonic hg_pos, β ^ (p ^ n) = β) :
    g.degree?.getD 0 ∣ n := by
  let d := g.degree?.getD 0
  let r := n % d
  by_cases hr_zero : r = 0
  · exact Nat.dvd_of_mod_eq_zero (by simpa [r, d] using hr_zero)
  · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_zero
    have hr_lt_d : r < d := by
      dsimp [r, d]
      exact Nat.mod_lt n hg_pos
    let f : FpPoly p := DensePoly.monomial (p ^ r) (1 : ZMod64 p) - FpPoly.X
    have hf_ne : f ≠ 0 := by
      dsimp [f]
      exact monomial_pPow_sub_X_ne_zero (p := p) hr_pos
    have hroot : ∀ β : Quotient g hmonic hg_pos,
        eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β = 0 := by
      intro β
      have hfixed_r :
          β ^ (p ^ r) = β := by
        simpa [r, d] using
          pow_pPow_mod_degree_eq_of_fixed
            (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr (h β)
      dsimp [f]
      rw [eval_sub, eval_monomial, eval_X]
      change (1 : Quotient g hmonic hg_pos) * β ^ (p ^ r) - β = 0
      rw [one_mul, hfixed_r, sub_self]
    have hfilter_eq :
        (elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos)).filter
            (fun β => decide
              (eval (g := g) (hmonic := hmonic) (hg_pos := hg_pos) f β = 0)) =
          elements (g := g) (hmonic := hmonic) (hg_pos := hg_pos) := by
      apply (List.filter_eq_self).mpr
      intro β _hβ
      exact decide_eq_true (hroot β)
    have hroot_bound :=
      eval_rootsIn_elements_length_le_degree
        (g := g) (hmonic := hmonic) (hg_pos := hg_pos) hg_irr f hf_ne
    rw [hfilter_eq, elements_card] at hroot_bound
    have hsize_bound : f.size - 1 ≤ p ^ r := by
      dsimp [f]
      exact monomial_pPow_sub_X_size_sub_one_le (p := p) hr_pos
    have hcard_le : p ^ d ≤ p ^ r := Nat.le_trans hroot_bound hsize_bound
    have hp_gt_one : 1 < p := by
      have hp_two : 2 ≤ p :=
        Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
      omega
    have hpow_lt : p ^ r < p ^ d := Nat.pow_lt_pow_right hp_gt_one hr_lt_d
    exact False.elim (Nat.not_lt_of_ge hcard_le hpow_lt)

end Internal

export Internal (eval eval_zero eval_C eval_X eval_add eval_sub eval_C_mul eval_monomial)

end Quotient
end FpPoly
end Hex
