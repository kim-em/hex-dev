/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.DriverCompleteness

public section

/-!
# Certified complex-root isolation example

This proof-facing example isolates all roots of `z³ - z - 1`.  Its real root
is the plastic constant (the smallest Pisot number): the certificates locate
it between `1.32471795` and `1.32471796`, locate the conjugate pair to eight
decimal places, and prove that both nonreal roots lie strictly inside the unit
disc. See `examples/HexRootsDemo.lean` for the corresponding runnable demo.
-/

namespace HexRootsMathlib.Examples

open Polynomial
open Hex

noncomputable section

/-- `x³ - x - 1`, whose real root is the smallest Pisot number. -/
def pisot : ZPoly :=
  DensePoly.monomial 3 1 - DensePoly.monomial 1 1 - DensePoly.C 1

theorem toPolyℂ_pisot : toPolyℂ pisot = X ^ 3 - X - 1 := by
  simp [pisot, toPolyℂ, monomial_one_right_eq_X_pow]

theorem toPolyℚ_pisot : HexPolyZMathlib.toPolyℚ pisot = X ^ 3 - X - 1 := by
  simp [pisot, HexPolyZMathlib.toPolyℚ, monomial_one_right_eq_X_pow]

theorem natDegree_pisot : (toPolyℂ pisot).natDegree = 3 := by
  rw [toPolyℂ_pisot,
    natDegree_sub_eq_left_of_natDegree_lt (by
      rw [natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num),
    natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num

theorem pisot_ne_zero : pisot ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ZPoly => p.coeff 3) h
  norm_num [pisot] at hcoeff

/-- The rational polynomial `x³ - x - 1` is separable, discharging the
executable isolator's simple-root precondition. -/
theorem pisot_simple : HasOnlySimpleRoots pisot := by
  rw [hasOnlySimpleRoots_iff_separable pisot pisot_ne_zero, toPolyℚ_pisot,
    separable_def']
  let a : Polynomial ℚ := 18 * X - 27
  let b : Polynomial ℚ := -(6 * X ^ 2) + 9 * X + 4
  have hbezout :
      a * (X ^ 3 - X - 1) + b * derivative (X ^ 3 - X - 1) = 23 := by
    simp only [a, b, derivative_sub, derivative_pow, derivative_X, derivative_one,
      map_natCast]
    ring
  refine ⟨C (23⁻¹) * a, C (23⁻¹) * b, ?_⟩
  calc
    _ = C (23⁻¹) *
        (a * (X ^ 3 - X - 1) + b * derivative (X ^ 3 - X - 1)) := by ring
    _ = C (23⁻¹) * 23 := by rw [hbezout]
    _ = C (23⁻¹) * C 23 := by rw [C_ofNat]
    _ = C (23⁻¹ * 23) := by rw [map_mul]
    _ = 1 := by norm_num

def pisotLowerSquare : DyadicSquare where
  re := .ofIntWithPrec (-91033924845) 37
  im := .ofIntWithPrec (-77279107697) 37
  prec := 33

def pisotUpperSquare : DyadicSquare where
  re := .ofIntWithPrec (-91033924845) 37
  im := .ofIntWithPrec 4829944231 33
  prec := 33

def pisotRealSquare : DyadicSquare where
  re := .ofIntWithPrec 182067849689 37
  im := 0
  prec := 33

theorem pisotLower_witness : nkWitness pisot pisotLowerSquare := by decide

theorem pisotUpper_witness : nkWitness pisot pisotUpperSquare := by decide

theorem pisotReal_witness : nkWitness pisot pisotRealSquare := by decide

noncomputable def pisotLowerRoot : ℂ :=
  (NKData.existsUnique_root pisotLower_witness).exists.choose

noncomputable def pisotUpperRoot : ℂ :=
  (NKData.existsUnique_root pisotUpper_witness).exists.choose

noncomputable def pisotRealRoot : ℂ :=
  (NKData.existsUnique_root pisotReal_witness).exists.choose

theorem pisotLowerRoot_spec :
    (toPolyℂ pisot).eval pisotLowerRoot = 0 ∧
      pisotLowerRoot ∈ DyadicSquare.closedSquare pisotLowerSquare :=
  (NKData.existsUnique_root pisotLower_witness).exists.choose_spec

theorem pisotUpperRoot_spec :
    (toPolyℂ pisot).eval pisotUpperRoot = 0 ∧
      pisotUpperRoot ∈ DyadicSquare.closedSquare pisotUpperSquare :=
  (NKData.existsUnique_root pisotUpper_witness).exists.choose_spec

theorem pisotRealRoot_spec :
    (toPolyℂ pisot).eval pisotRealRoot = 0 ∧
      pisotRealRoot ∈ DyadicSquare.closedSquare pisotRealSquare :=
  (NKData.existsUnique_root pisotReal_witness).exists.choose_spec

theorem pisotLowerRoot_bounds :
    (-66235899 / 100000000 : ℝ) < pisotLowerRoot.re ∧
      pisotLowerRoot.re < (-66235897 / 100000000 : ℝ) ∧
      (-56227953 / 100000000 : ℝ) < pisotLowerRoot.im ∧
      pisotLowerRoot.im < (-56227950 / 100000000 : ℝ) := by
  obtain ⟨hre, him⟩ :=
    (DyadicSquare.mem_closedSquare_iff_re_im pisotLowerSquare pisotLowerRoot).mp
      pisotLowerRoot_spec.2
  rw [abs_le] at hre him
  norm_num [pisotLowerSquare, DyadicSquare.halfWidth,
    Hex.DyadicSquare.halfWidth, Dyadic.toReal_ofIntWithPrec] at hre him
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem pisotUpperRoot_bounds :
    (-66235899 / 100000000 : ℝ) < pisotUpperRoot.re ∧
      pisotUpperRoot.re < (-66235897 / 100000000 : ℝ) ∧
      (56227950 / 100000000 : ℝ) < pisotUpperRoot.im ∧
      pisotUpperRoot.im < (56227953 / 100000000 : ℝ) := by
  obtain ⟨hre, him⟩ :=
    (DyadicSquare.mem_closedSquare_iff_re_im pisotUpperSquare pisotUpperRoot).mp
      pisotUpperRoot_spec.2
  rw [abs_le] at hre him
  norm_num [pisotUpperSquare, DyadicSquare.halfWidth,
    Hex.DyadicSquare.halfWidth, Dyadic.toReal_ofIntWithPrec] at hre him
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem pisotRealRoot_bounds :
    (132471795 / 100000000 : ℝ) < pisotRealRoot.re ∧
      pisotRealRoot.re < (132471796 / 100000000 : ℝ) := by
  have hre :=
    (DyadicSquare.mem_closedSquare_iff_re_im pisotRealSquare pisotRealRoot).mp
      pisotRealRoot_spec.2 |>.1
  rw [abs_le] at hre
  norm_num [pisotRealSquare, DyadicSquare.halfWidth,
    Hex.DyadicSquare.halfWidth, Dyadic.toReal_ofIntWithPrec] at hre
  constructor <;> linarith

/-- The root in the real-centred certificate is genuinely real: conjugation
preserves both its equation and its certified square, so uniqueness fixes it. -/
theorem pisotRealRoot_im : pisotRealRoot.im = 0 := by
  have hconjRoot :
      (toPolyℂ pisot).eval (starRingEnd ℂ pisotRealRoot) = 0 := by
    have hroot := pisotRealRoot_spec.1
    rw [toPolyℂ_pisot] at hroot ⊢
    simpa using congrArg (starRingEnd ℂ) hroot
  have hcoords :=
    (DyadicSquare.mem_closedSquare_iff_re_im pisotRealSquare pisotRealRoot).mp
      pisotRealRoot_spec.2
  have hconjMem : starRingEnd ℂ pisotRealRoot ∈
      DyadicSquare.closedSquare pisotRealSquare := by
    rw [DyadicSquare.mem_closedSquare_iff_re_im]
    constructor
    · simpa using hcoords.1
    · simpa [pisotRealSquare] using hcoords.2
  have hfixed : starRingEnd ℂ pisotRealRoot = pisotRealRoot :=
    (NKData.existsUnique_root pisotReal_witness).unique
      ⟨hconjRoot, hconjMem⟩ pisotRealRoot_spec
  exact Complex.conj_eq_iff_im.mp hfixed

theorem pisotLowerRoot_norm : ‖pisotLowerRoot‖ < 1 := by
  have hb := pisotLowerRoot_bounds
  have hre : |pisotLowerRoot.re| < (663 / 1000 : ℝ) := by
    rw [abs_of_neg (by linarith [hb.2.1])]
    linarith [hb.1]
  have him : |pisotLowerRoot.im| < (563 / 1000 : ℝ) := by
    rw [abs_of_neg (by linarith [hb.2.2.2])]
    linarith [hb.2.2.1]
  have hreSq : pisotLowerRoot.re ^ 2 < (663 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_abs pisotLowerRoot.re]
  have himSq : pisotLowerRoot.im ^ 2 < (563 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_abs pisotLowerRoot.im]
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

theorem pisotUpperRoot_norm : ‖pisotUpperRoot‖ < 1 := by
  have hb := pisotUpperRoot_bounds
  have hre : |pisotUpperRoot.re| < (663 / 1000 : ℝ) := by
    rw [abs_of_neg (by linarith [hb.2.1])]
    linarith [hb.1]
  have him : |pisotUpperRoot.im| < (563 / 1000 : ℝ) := by
    rw [abs_of_pos (by linarith [hb.2.2.1])]
    linarith [hb.2.2.2]
  have hreSq : pisotUpperRoot.re ^ 2 < (663 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_abs pisotUpperRoot.re]
  have himSq : pisotUpperRoot.im ^ 2 < (563 / 1000 : ℝ) ^ 2 := by
    nlinarith [sq_abs pisotUpperRoot.im]
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- The three explicit Newton certificates account for every complex root of
`x³ - x - 1`. -/
theorem pisot_roots :
    (toPolyℂ pisot).roots.toFinset =
      {pisotRealRoot, pisotLowerRoot, pisotUpperRoot} := by
  have hp : toPolyℂ pisot ≠ 0 := by
    rw [toPolyℂ_pisot]
    intro h
    have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff 3) h
    norm_num at hcoeff
    rw [coeff_X, coeff_one] at hcoeff
    norm_num at hcoeff
  have hlower : pisotLowerRoot ∈ (toPolyℂ pisot).roots.toFinset :=
    Multiset.mem_toFinset.mpr <| (mem_roots hp).mpr pisotLowerRoot_spec.1
  have hupper : pisotUpperRoot ∈ (toPolyℂ pisot).roots.toFinset :=
    Multiset.mem_toFinset.mpr <| (mem_roots hp).mpr pisotUpperRoot_spec.1
  have hreal : pisotRealRoot ∈ (toPolyℂ pisot).roots.toFinset :=
    Multiset.mem_toFinset.mpr <| (mem_roots hp).mpr pisotRealRoot_spec.1
  have hlu : pisotLowerRoot ≠ pisotUpperRoot := by
    intro h
    have him := congrArg Complex.im h
    linarith [pisotLowerRoot_bounds.2.2.2, pisotUpperRoot_bounds.2.2.1]
  have hlr : pisotLowerRoot ≠ pisotRealRoot := by
    intro h
    have him := congrArg Complex.im h
    rw [pisotRealRoot_im] at him
    linarith [pisotLowerRoot_bounds.2.2.2]
  have hur : pisotUpperRoot ≠ pisotRealRoot := by
    intro h
    have him := congrArg Complex.im h
    rw [pisotRealRoot_im] at him
    linarith [pisotUpperRoot_bounds.2.2.1]
  let certified : Finset ℂ :=
    {pisotRealRoot, pisotLowerRoot, pisotUpperRoot}
  have hsubset : certified ⊆ (toPolyℂ pisot).roots.toFinset := by
    intro z hz
    simp only [certified, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl | rfl)
    · exact hreal
    · exact hlower
    · exact hupper
  have hcertified : certified.card = 3 := by
    simp [certified, Ne.symm hlr, Ne.symm hur, hlu]
  have hrootsCard : (toPolyℂ pisot).roots.toFinset.card ≤ 3 := by
    calc
      _ ≤ (toPolyℂ pisot).roots.card := Multiset.toFinset_card_le _
      _ ≤ (toPolyℂ pisot).natDegree := card_roots' _
      _ = 3 := natDegree_pisot
  exact (Finset.eq_of_subset_of_card_le hsubset
    (by simpa [hcertified] using hrootsCard)).symm

/-- The full driver succeeds, returns three atoms, and its semantic roots are
the three explicitly bounded roots above. -/
theorem isolate_pisot :
    ∃ atoms : Array (DyadicRootIsolation pisot),
      isolate pisot pisot_simple 32 .nk = some atoms ∧
      atoms.size = 3 ∧
      (atoms.toList.map HexRootsMathlib.DyadicRootIsolation.root).toFinset =
        {pisotRealRoot, pisotLowerRoot, pisotUpperRoot} ∧
      ∀ iso ∈ atoms.toList, 32 ≤ iso.square.prec := by
  obtain ⟨atoms, hrun, hcount, hroots, hprec⟩ :=
    isolate_spec pisot pisot_simple pisot_ne_zero 32 .nk
  exact ⟨atoms, hrun, hcount.trans natDegree_pisot,
    hroots.trans pisot_roots, hprec⟩

/-- A compact statement of the Pisot example: the real root is pinned to
eight decimal places and every other root lies strictly inside the unit disc. -/
theorem pisot_property :
    (132471795 / 100000000 : ℝ) < pisotRealRoot.re ∧
      pisotRealRoot.re < (132471796 / 100000000 : ℝ) ∧
      pisotRealRoot.im = 0 ∧
      ∀ z ∈ (toPolyℂ pisot).roots.toFinset,
        z ≠ pisotRealRoot → ‖z‖ < 1 := by
  refine ⟨pisotRealRoot_bounds.1, pisotRealRoot_bounds.2,
    pisotRealRoot_im, ?_⟩
  intro z hz hne
  rw [pisot_roots] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with (rfl | rfl | rfl)
  · exact (hne rfl).elim
  · exact pisotLowerRoot_norm
  · exact pisotUpperRoot_norm

end

end HexRootsMathlib.Examples
