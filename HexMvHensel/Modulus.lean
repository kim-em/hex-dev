/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvHensel.Shift
public import HexModular.SymMod

@[expose] public section

/-!
Coefficient reduction and the two congruence relations used by multivariate
Hensel lifting.

`CongrAt` observes the total degree in all non-main variables, while
`BoxCongr` observes the coordinatewise box computed by `truncate`.  Keeping
the predicates distinct prevents a box-truncated intermediate from being
mistaken for a representative modulo a power of the evaluation ideal.
-/

namespace Hex.MvHensel

open Hex.MvPoly

variable {n : Nat}
  {cmp : Mono (n + 1) → Mono (n + 1) → Ordering}
  [IsMonomialOrder cmp]

/-- Replace every coefficient by its symmetric representative modulo `m`,
deleting terms whose representative is zero. -/
def reduceMod (m : Nat) (p : MvPoly (n + 1) Int cmp) :
    MvPoly (n + 1) Int cmp :=
  MvPoly.mapCoeffs (fun c => Hex.Modular.symMod c m) p

/-- The exact symmetric interval `(-m/2, m/2]`, written without division so
the even-modulus endpoint convention is explicit. -/
def SymCanonical (m : Nat) (p : MvPoly (n + 1) Int cmp) : Prop :=
  ∀ u : Mono (n + 1),
    -(m : Int) < 2 * MvPoly.coeff u p ∧
      2 * MvPoly.coeff u p ≤ (m : Int)

/-- Total exponent in all variables other than `i`. -/
def nonMainDegree (i : Fin (n + 1)) (u : Mono (n + 1)) : Nat :=
  (List.finRange n).foldl
    (fun degree j => degree + Mono.degreeOf (remainingVar i j) u) 0

/-- Coefficients of `p` and `q` agree modulo `m` through total non-main
degree `k`. -/
def CongrAt (i : Fin (n + 1)) (k m : Nat)
    (p q : MvPoly (n + 1) Int cmp) : Prop :=
  ∀ u : Mono (n + 1), nonMainDegree i u ≤ k →
    (MvPoly.coeff u p - MvPoly.coeff u q) % (m : Int) = 0

/-- Coefficients of `p` and `q` agree modulo `m` throughout the
coordinatewise non-main degree box `d`. -/
def BoxCongr (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    (p q : MvPoly (n + 1) Int cmp) : Prop :=
  ∀ u : Mono (n + 1),
    (∀ j : Fin n, Mono.degreeOf (remainingVar i j) u ≤ d j) →
      (MvPoly.coeff u p - MvPoly.coeff u q) % (m : Int) = 0

private theorem modDiff_symm {a b : Int} {m : Nat}
    (h : (a - b) % (m : Int) = 0) :
    (b - a) % (m : Int) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  rw [show b - a = -(a - b) by omega]
  exact Int.dvd_neg.mpr (Int.dvd_of_emod_eq_zero h)

private theorem modDiff_trans {a b c : Int} {m : Nat}
    (hab : (a - b) % (m : Int) = 0)
    (hbc : (b - c) % (m : Int) = 0) :
    (a - c) % (m : Int) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  rw [show a - c = (a - b) + (b - c) by omega]
  exact Int.dvd_add (Int.dvd_of_emod_eq_zero hab)
    (Int.dvd_of_emod_eq_zero hbc)

private theorem modDiff_add {a b c d : Int} {m : Nat}
    (hab : (a - b) % (m : Int) = 0)
    (hcd : (c - d) % (m : Int) = 0) :
    ((a + c) - (b + d)) % (m : Int) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  rw [show (a + c) - (b + d) = (a - b) + (c - d) by omega]
  exact Int.dvd_add (Int.dvd_of_emod_eq_zero hab)
    (Int.dvd_of_emod_eq_zero hcd)

private theorem modDiff_mul {a b c d : Int} {m : Nat}
    (hab : (a - b) % (m : Int) = 0)
    (hcd : (c - d) % (m : Int) = 0) :
    (a * c - b * d) % (m : Int) = 0 := by
  apply Int.emod_eq_zero_of_dvd
  rw [show a * c - b * d = (a - b) * c + b * (c - d) by grind]
  exact Int.dvd_add
    (Int.dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero hab))
    (Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero hcd))

private theorem foldlModDiff {A : Type} (xs : List A) (f g : A → Int)
    {a b : Int} {m : Nat} (hab : (a - b) % (m : Int) = 0)
    (hfg : ∀ x, x ∈ xs → (f x - g x) % (m : Int) = 0) :
    (xs.foldl (fun acc x => acc + f x) a -
      xs.foldl (fun acc x => acc + g x) b) % (m : Int) = 0 := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (modDiff_add hab (hfg x (List.mem_cons_self ..)))
      intro y hy
      exact hfg y (List.mem_cons_of_mem x hy)

private theorem foldlAdd_le {A : Type} (xs : List A) (f g : A → Nat)
    {a b : Nat} (hab : a ≤ b) (hfg : ∀ x, x ∈ xs → f x ≤ g x) :
    xs.foldl (fun acc x => acc + f x) a ≤
      xs.foldl (fun acc x => acc + g x) b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih (Nat.add_le_add hab (hfg x (List.mem_cons_self ..)))
      intro y hy
      exact hfg y (List.mem_cons_of_mem x hy)

private theorem nonMainDegree_le_parts (i : Fin (n + 1))
    {a b u : Mono (n + 1)} (hmul : Mono.mul a b = u) :
    nonMainDegree i a ≤ nonMainDegree i u ∧
      nonMainDegree i b ≤ nonMainDegree i u := by
  have hcoord (j : Fin n) :
      Mono.degreeOf (remainingVar i j) a ≤
          Mono.degreeOf (remainingVar i j) u ∧
        Mono.degreeOf (remainingVar i j) b ≤
          Mono.degreeOf (remainingVar i j) u := by
    have hget := congrArg
      (fun x : Mono (n + 1) => x[remainingVar i j]) hmul
    simp only [Mono.getElem_mul] at hget
    change a[remainingVar i j] ≤ u[remainingVar i j] ∧
      b[remainingVar i j] ≤ u[remainingVar i j]
    constructor <;> omega
  unfold nonMainDegree
  constructor
  · apply foldlAdd_le _ _ _ (Nat.le_refl 0)
    intro j _
    exact (hcoord j).1
  · apply foldlAdd_le _ _ _ (Nat.le_refl 0)
    intro j _
    exact (hcoord j).2

private theorem symMod_zero (m : Nat) : Hex.Modular.symMod 0 m = 0 := by
  unfold Hex.Modular.symMod
  split <;> simp_all

private theorem symMod_modDiff (a : Int) (m : Nat) :
    (Hex.Modular.symMod a m - a) % (m : Int) = 0 := by
  cases m with
  | zero => simp [Hex.Modular.symMod]
  | succ m =>
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mp
      exact Hex.Modular.symMod_emod (by omega)

/-! Ideal-adic congruence laws. -/

theorem congrAt_refl (i : Fin (n + 1)) (k m : Nat)
    (p : MvPoly (n + 1) Int cmp) : CongrAt i k m p p := by
  intro u _
  simp

theorem congrAt_symm {i : Fin (n + 1)} {k m : Nat}
    {p q : MvPoly (n + 1) Int cmp} :
    CongrAt i k m p q → CongrAt i k m q p := by
  intro hpq u hu
  exact modDiff_symm (hpq u hu)

theorem congrAt_trans {i : Fin (n + 1)} {k m : Nat}
    {p q r : MvPoly (n + 1) Int cmp} :
    CongrAt i k m p q → CongrAt i k m q r → CongrAt i k m p r := by
  intro hpq hqr u hu
  exact modDiff_trans (hpq u hu) (hqr u hu)

theorem congrAt_add {i : Fin (n + 1)} {k m : Nat}
    {p p' q q' : MvPoly (n + 1) Int cmp}
    (hp : CongrAt i k m p p') (hq : CongrAt i k m q q') :
    CongrAt i k m (p + q) (p' + q') := by
  intro u hu
  rw [MvPoly.coeff_add, MvPoly.coeff_add]
  exact modDiff_add (hp u hu) (hq u hu)

theorem congrAt_mul {i : Fin (n + 1)} {k m : Nat}
    {p p' q q' : MvPoly (n + 1) Int cmp}
    (hp : CongrAt i k m p p') (hq : CongrAt i k m q q') :
    CongrAt i k m (p * q) (p' * q') := by
  intro u hu
  rw [MvPoly.coeff_mul, MvPoly.coeff_mul]
  apply foldlModDiff _ _ _ (by simp)
  intro ab hab
  have hparts := nonMainDegree_le_parts i
    ((Mono.splits_mem_iff u ab.1 ab.2).mp hab)
  exact modDiff_mul (hp ab.1 (Nat.le_trans hparts.1 hu))
    (hq ab.2 (Nat.le_trans hparts.2 hu))

theorem congrAt_reduceMod (i : Fin (n + 1)) (k m : Nat)
    (p : MvPoly (n + 1) Int cmp) :
    CongrAt i k m (reduceMod m p) p := by
  intro u _
  unfold reduceMod
  rw [MvPoly.coeff_mapCoeffs (symMod_zero m)]
  exact symMod_modDiff _ _

theorem congrAt_mono {i : Fin (n + 1)} {k k' m : Nat}
    {p q : MvPoly (n + 1) Int cmp} (h : k' ≤ k)
    (hpq : CongrAt i k m p q) : CongrAt i k' m p q := by
  intro u hu
  exact hpq u (Nat.le_trans hu h)

/-! Box congruence laws. -/

theorem boxCongr_refl (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    (p : MvPoly (n + 1) Int cmp) : BoxCongr i d m p p := by
  intro u _
  simp

theorem boxCongr_symm {i : Fin (n + 1)} {d : Fin n → Nat} {m : Nat}
    {p q : MvPoly (n + 1) Int cmp} :
    BoxCongr i d m p q → BoxCongr i d m q p := by
  intro hpq u hu
  exact modDiff_symm (hpq u hu)

theorem boxCongr_trans {i : Fin (n + 1)} {d : Fin n → Nat} {m : Nat}
    {p q r : MvPoly (n + 1) Int cmp} :
    BoxCongr i d m p q → BoxCongr i d m q r → BoxCongr i d m p r := by
  intro hpq hqr u hu
  exact modDiff_trans (hpq u hu) (hqr u hu)

theorem boxCongr_add {i : Fin (n + 1)} {d : Fin n → Nat} {m : Nat}
    {p p' q q' : MvPoly (n + 1) Int cmp}
    (hp : BoxCongr i d m p p') (hq : BoxCongr i d m q q') :
    BoxCongr i d m (p + q) (p' + q') := by
  intro u hu
  rw [MvPoly.coeff_add, MvPoly.coeff_add]
  exact modDiff_add (hp u hu) (hq u hu)

theorem boxCongr_mul {i : Fin (n + 1)} {d : Fin n → Nat} {m : Nat}
    {p p' q q' : MvPoly (n + 1) Int cmp}
    (hp : BoxCongr i d m p p') (hq : BoxCongr i d m q q') :
    BoxCongr i d m (p * q) (p' * q') := by
  intro u hu
  rw [MvPoly.coeff_mul, MvPoly.coeff_mul]
  apply foldlModDiff _ _ _ (by simp)
  intro ab hab
  have hmul := (Mono.splits_mem_iff u ab.1 ab.2).mp hab
  have hcoord (j : Fin n) :
      Mono.degreeOf (remainingVar i j) ab.1 ≤
          Mono.degreeOf (remainingVar i j) u ∧
        Mono.degreeOf (remainingVar i j) ab.2 ≤
          Mono.degreeOf (remainingVar i j) u := by
    have hget := congrArg
      (fun x : Mono (n + 1) => x[remainingVar i j]) hmul
    simp only [Mono.getElem_mul] at hget
    change ab.1[remainingVar i j] ≤ u[remainingVar i j] ∧
      ab.2[remainingVar i j] ≤ u[remainingVar i j]
    constructor <;> omega
  exact modDiff_mul
    (hp ab.1 (fun j => Nat.le_trans (hcoord j).1 (hu j)))
    (hq ab.2 (fun j => Nat.le_trans (hcoord j).2 (hu j)))

theorem boxCongr_reduceMod (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    (p : MvPoly (n + 1) Int cmp) :
    BoxCongr i d m (reduceMod m p) p := by
  intro u _
  unfold reduceMod
  rw [MvPoly.coeff_mapCoeffs (symMod_zero m)]
  exact symMod_modDiff _ _

/-- Truncating is invisible inside the truncation box. -/
theorem boxCongr_truncate (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    (p : MvPoly (n + 1) Int cmp) :
    BoxCongr i d m (truncate i d p) p := by
  intro u hu
  rw [coeff_truncate, Hex.ite_eq_left hu, Int.sub_self, Int.zero_emod]

/-- Total-degree congruence through the sum of the side degrees implies box
congruence.  The converse is false. -/
theorem boxCongr_of_congrAt (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    {p q : MvPoly (n + 1) Int cmp}
    (h : CongrAt i ((List.finRange n).foldl (fun s j => s + d j) 0) m p q) :
    BoxCongr i d m p q := by
  intro u hu
  apply h u
  unfold nonMainDegree
  exact foldlAdd_le _ _ _ (Nat.le_refl 0) (fun j _ => hu j)

/-- Symmetric reduction lands in the exact canonical interval.  Positivity is
necessary: at modulus zero the interval `(-m/2,m/2]` is empty. -/
theorem reduceMod_symCanonical (m : Nat) (hm : 0 < m)
    (p : MvPoly (n + 1) Int cmp) :
    SymCanonical m (reduceMod m p) := by
  intro u
  unfold reduceMod
  rw [MvPoly.coeff_mapCoeffs (symMod_zero m)]
  let x := Hex.Modular.symMod (MvPoly.coeff u p) m
  have hbound : 2 * x.natAbs ≤ m := Hex.Modular.symMod_le hm
  have hbound' : ((2 * x.natAbs : Nat) : Int) ≤ (m : Int) :=
    Int.ofNat_le.mpr hbound
  have hlower : -(m : Int) < 2 * x := by
    unfold x Hex.Modular.symMod
    rw [Hex.ite_eq_right (Nat.ne_of_gt hm)]
    simp only
    have hrem : 0 ≤ MvPoly.coeff u p % (m : Int) :=
      Int.emod_nonneg _ (by omega)
    split <;> omega
  constructor
  · exact hlower
  by_cases hx : 0 ≤ x
  · rw [Int.natCast_mul, Int.ofNat_natAbs_of_nonneg hx] at hbound'
    exact hbound'
  · omega

private theorem eq_of_symBounds {a b : Int} {m : Nat}
    (ha : -(m : Int) < 2 * a ∧ 2 * a ≤ (m : Int))
    (hb : -(m : Int) < 2 * b ∧ 2 * b ≤ (m : Int))
    (hab : (a - b) % (m : Int) = 0) : a = b := by
  have hm : 0 < m := by omega
  have hdvd : (m : Int) ∣ a - b := Int.dvd_of_emod_eq_zero hab
  have hlt : (a - b).natAbs < m := by
    by_cases hnonneg : 0 ≤ a - b
    · rw [← Int.ofNat_lt, Int.ofNat_natAbs_of_nonneg hnonneg]
      omega
    · have hnonpos : a - b ≤ 0 := by omega
      rw [← Int.ofNat_lt, Int.ofNat_natAbs_of_nonpos hnonpos]
      omega
  have hzero : a - b = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    simpa using hlt
  omega

/-- Reducing an already symmetric-canonical polynomial changes nothing. -/
theorem reduceMod_id (m : Nat) (p : MvPoly (n + 1) Int cmp)
    (h : SymCanonical m p) : reduceMod m p = p := by
  have hm : 0 < m := by
    have hz := h Mono.zero
    omega
  apply MvPoly.ext
  intro u
  have hcanonical := reduceMod_symCanonical m hm p u
  exact eq_of_symBounds hcanonical (h u) (by
    unfold reduceMod
    rw [MvPoly.coeff_mapCoeffs (symMod_zero m)]
    exact symMod_modDiff _ _)

end Hex.MvHensel
