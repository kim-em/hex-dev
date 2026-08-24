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
  sorry

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
  sorry

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
  rw [coeff_truncate, if_pos hu, Int.sub_self, Int.zero_emod]

/-- Total-degree congruence through the sum of the side degrees implies box
congruence.  The converse is false. -/
theorem boxCongr_of_congrAt (i : Fin (n + 1)) (d : Fin n → Nat) (m : Nat)
    {p q : MvPoly (n + 1) Int cmp}
    (h : CongrAt i ((List.finRange n).foldl (fun s j => s + d j) 0) m p q) :
    BoxCongr i d m p q := by
  sorry

/-- Symmetric reduction lands in the exact canonical interval.  Positivity is
necessary: at modulus zero the interval `(-m/2,m/2]` is empty. -/
theorem reduceMod_symCanonical (m : Nat) (hm : 0 < m)
    (p : MvPoly (n + 1) Int cmp) :
    SymCanonical m (reduceMod m p) := by
  sorry

/-- Reducing an already symmetric-canonical polynomial changes nothing. -/
theorem reduceMod_id (m : Nat) (p : MvPoly (n + 1) Int cmp)
    (h : SymCanonical m p) : reduceMod m p = p := by
  sorry

end Hex.MvHensel
