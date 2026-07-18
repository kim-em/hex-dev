/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealRootsMathlib.ChainCorrespond
import HexRealRootsMathlib.Isolations

/-!
Companion conformance checks for `HexRealRootsMathlib`.

Oracle: none; checked against Mathlib root counts via the proven
correspondence theorems. `rootCount_eq_card_roots` (and `squareFreeRat_iff` feeding its
square-free hypothesis) is the bridge that ties the executable, computable
`Hex.rootCount` to the noncomputable Mathlib `(toPolyℝ p).roots.card`. There is
no external oracle profile: the two sides are pinned independently — the
executable side by `#guard` (native evaluation) and the Mathlib side by a
hand-derived root-multiset computation proven as a theorem — and the correspond-
ence theorem certifies they agree.
Mode: always for core.

Covered operations:
* `Hex.rootCount`, the executable real-root count, tied to the noncomputable
  Mathlib count `(toPolyℝ p).roots.card` by `rootCount_eq_card_roots`.

Covered properties:
* `rootCount p = (toPolyℝ p).roots.card`, the root-count correspondence,
  instantiated per fixture (executable side `#guard`ed, Mathlib side proven as a
  theorem from an independent factorisation).
* the full formal tie on `x - 5`: `Hex.rootCount = 1` derived through
  `rootCount_eq_card_roots` and `squareFreeRat_iff`, not read off evaluation.

Covered edge cases:
* degree-0 nonzero constant (`const7 = 7`), below the correspondence theorem's
  positive-degree hypothesis: no roots, executable count `0`.
* a polynomial with no real roots (`quadNone = x^2 + 1`): count `0`.
* a polynomial with several distinct real roots (`cubicTriple = x^3 - x`):
  count `3`.

Because Mathlib root counts are noncomputable, the checks are **theorems**, not
`#guard`s of the root multiset. For each committed fixture:

* `toPolyℝ_<fixture>` identifies the real cast of the executable polynomial with
  an explicit `Polynomial ℝ` (mechanical `coeff` comparison).
* `card_<fixture>` computes `(toPolyℝ <fixture>).roots.card` from that explicit
  polynomial by an independent Mathlib factorisation (the hand-derived count).
* `#guard Hex.rootCount <fixture> = N` confirms the executable engine computes
  the same `N` at runtime.

This module certifies that the **theorem layer** connects — that the
correspondence theorems instantiate and transport concrete counts — rather than
re-running the executable oracle (which is `HexRealRoots.Conformance`'s job).
The `x − 5` fixture carries the full formal tie: `rootCount_x_sub_5` derives
`Hex.rootCount = 1` from `rootCount_eq_card_roots` and the independent
`card_linear`, so the executable value (also `#guard`ed) is pinned by the
theorem, not just by evaluation. The higher-degree fixtures certify each side
independently against the same hand-derived count; their full ties would need a
square-free proof of each rational cast, which the linear demonstrator already
exhibits end to end.
-/

namespace HexRealRootsMathlib
namespace Conformance

open Polynomial

/-! ### Committed fixtures.

Stored in ascending-degree coefficient order; the factored form and real roots
are named so the Mathlib-side counts are hand-derivable. -/

/-- `x − 5`; single real root `5`. -/
private def linear : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(-5 : Int), 1]
/-- `x² − 1 = (x − 1)(x + 1)`; real roots `±1`. -/
private def quadPair : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(-1 : Int), 0, 1]
/-- `x² + 1`; no real roots. -/
private def quadNone : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(1 : Int), 0, 1]
/-- `x³ − x = x(x − 1)(x + 1)`; real roots `−1, 0, 1`. -/
private def cubicTriple : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(0 : Int), -1, 0, 1]
/-- The nonzero constant `7`; no roots (degree `0`, below the correspondence
theorem's positive-degree hypothesis). -/
private def const7 : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(7 : Int)]

/-! ### Real casts: the executable polynomial as an explicit `Polynomial ℝ`. -/

private theorem toPolyℝ_linear : toPolyℝ linear = X - C 5 := by
  apply Polynomial.ext; intro n
  rw [coeff_toPolyℝ]
  simp only [linear, Hex.DensePoly.coeff_ofCoeffs, coeff_sub, coeff_X, coeff_C]
  match n with
  | 0 => norm_num [Array.getD]
  | 1 => norm_num [Array.getD]
  | (k + 2) => norm_num [Array.getD]; omega

private theorem toPolyℝ_quadPair : toPolyℝ quadPair = X ^ 2 - C 1 := by
  apply Polynomial.ext; intro n
  rw [coeff_toPolyℝ]
  simp only [quadPair, Hex.DensePoly.coeff_ofCoeffs, coeff_sub, coeff_X_pow, coeff_C]
  match n with
  | 0 => norm_num [Array.getD]
  | 1 => norm_num [Array.getD]
  | 2 => norm_num [Array.getD]
  | (k + 3) => norm_num [Array.getD]; omega

private theorem toPolyℝ_quadNone : toPolyℝ quadNone = X ^ 2 + C 1 := by
  apply Polynomial.ext; intro n
  rw [coeff_toPolyℝ]
  simp only [quadNone, Hex.DensePoly.coeff_ofCoeffs, coeff_add, coeff_X_pow, coeff_C]
  match n with
  | 0 => norm_num [Array.getD]
  | 1 => norm_num [Array.getD]
  | 2 => norm_num [Array.getD]
  | (k + 3) => norm_num [Array.getD]; omega

private theorem toPolyℝ_cubicTriple : toPolyℝ cubicTriple = X ^ 3 - X := by
  apply Polynomial.ext; intro n
  rw [coeff_toPolyℝ]
  simp only [cubicTriple, Hex.DensePoly.coeff_ofCoeffs, coeff_sub, coeff_X_pow, coeff_X]
  match n with
  | 0 => norm_num [Array.getD]
  | 1 => norm_num [Array.getD]
  | 2 => norm_num [Array.getD]
  | 3 => norm_num [Array.getD]
  | (k + 4) => norm_num [Array.getD]; omega

private theorem toPolyℝ_const7 : toPolyℝ const7 = C 7 := by
  apply Polynomial.ext; intro n
  rw [coeff_toPolyℝ]
  simp only [const7, Hex.DensePoly.coeff_ofCoeffs, coeff_C]
  match n with
  | 0 => norm_num [Array.getD]
  | (k + 1) => norm_num [Array.getD]

/-! ### Mathlib-side root counts (hand-derived by factorisation). -/

private theorem card_linear : (toPolyℝ linear).roots.card = 1 := by
  rw [toPolyℝ_linear, roots_X_sub_C]; simp

private theorem card_quadPair : (toPolyℝ quadPair).roots.card = 2 := by
  rw [toPolyℝ_quadPair,
    show (X ^ 2 - C 1 : ℝ[X]) = (X - C 1) * (X + C 1) by
      have h : (X - C (1 : ℝ)) * (X + C 1) = X ^ 2 - C 1 * C 1 := by ring
      rw [h, ← map_mul, mul_one]]
  rw [roots_mul (by
    apply mul_ne_zero <;> intro h <;> simpa using congrArg (Polynomial.eval 0) h)]
  rw [roots_X_sub_C, show (X + C (1 : ℝ)) = X - C (-1) by rw [map_neg]; ring, roots_X_sub_C]
  simp

private theorem card_quadNone : (toPolyℝ quadNone).roots.card = 0 := by
  rw [toPolyℝ_quadNone, Multiset.card_eq_zero]
  by_contra hne0
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne0
  have hne : (X ^ 2 + C (1 : ℝ)) ≠ 0 := by
    intro h; simpa using congrArg (Polynomial.eval 0) h
  have hroot := (Polynomial.mem_roots hne).mp hx
  simp only [Polynomial.IsRoot, eval_add, eval_pow, eval_X, eval_C] at hroot
  nlinarith [sq_nonneg x]

private theorem card_cubicTriple : (toPolyℝ cubicTriple).roots.card = 3 := by
  rw [toPolyℝ_cubicTriple,
    show (X ^ 3 - X : ℝ[X]) = X * (X - C 1) * (X + C 1) by
      have h : X * (X - C (1 : ℝ)) * (X + C 1) = X ^ 3 - X * (C 1 * C 1) := by ring
      rw [h, ← map_mul, mul_one, map_one, mul_one]]
  have h1 : (X * (X - C 1) * (X + C 1) : ℝ[X]) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact X_ne_zero
      · intro h; simpa using congrArg (Polynomial.eval 0) h
    · intro h; simpa using congrArg (Polynomial.eval 0) h
  rw [roots_mul h1, roots_mul (by
    apply mul_ne_zero
    · exact X_ne_zero
    · intro h; simpa using congrArg (Polynomial.eval 0) h)]
  rw [roots_X, roots_X_sub_C, show (X + C (1 : ℝ)) = X - C (-1) by rw [map_neg]; ring,
    roots_X_sub_C]
  simp

private theorem card_const7 : (toPolyℝ const7).roots.card = 0 := by
  rw [toPolyℝ_const7, roots_C]; simp

/-! ### Executable root counts agree with the Mathlib counts (runtime). -/

#guard Hex.rootCount linear = 1
#guard Hex.rootCount quadPair = 2
#guard Hex.rootCount quadNone = 0
#guard Hex.rootCount cubicTriple = 3
#guard Hex.rootCount const7 = 0

/-! ### The full formal tie on the linear fixture.

`rootCount_eq_card_roots` needs a `SquareFreeRat` witness; for `x − 5` it comes
from `squareFreeRat_iff` and the irreducibility of the linear rational cast.
Chained with `card_linear`, the correspondence theorem pins the executable
`Hex.rootCount` to `1` as a theorem — the same value the `#guard` above
evaluates. -/

private theorem toPolyℚ_linear : toPolyℚ linear = X - C 5 := by
  apply Polynomial.ext; intro n
  rw [Polynomial.coeff_map, HexPolyZMathlib.coeff_toPolynomial]
  simp only [linear, Hex.DensePoly.coeff_ofCoeffs, coeff_sub, coeff_X, coeff_C]
  match n with
  | 0 => norm_num [Array.getD]
  | 1 => norm_num [Array.getD]
  | (k + 2) => norm_num [Array.getD]; omega

private theorem squareFreeRat_linear : Hex.ZPoly.SquareFreeRat linear := by
  rw [squareFreeRat_iff linear (by decide)]
  rw [toPolyℚ_linear]
  exact (irreducible_X_sub_C (5 : ℚ)).squarefree

private theorem rootCount_x_sub_5 : Hex.rootCount linear = 1 := by
  rw [rootCount_eq_card_roots linear (by decide) squareFreeRat_linear, card_linear]

/-! ### End-to-end ergonomics regression on `x⁴ − 2`.

This exercises the caller-facing API added for isolating the real roots of a
concrete polynomial, so the "one certified interval, `simp`" path stays green:

* the Sturm squarefree certificate `squareFreeRat_of_hasSquarefreeSturmChain`,
  discharged by `by decide` on the executable chain (no rational gcd);
* the coefficient-sum `eval_toPolyℝ` bridge, turning `IsRoot` into `x⁴ − 2 = 0`;
* the `toReal_ofInt_shiftRight` simp lemma for the `k / 2²⁰` dyadic endpoints;
* the `Hex`-namespace dot-notation alias `RealRootIsolation.exists_unique_root`.

The tight interval `(1246974/2²⁰, 1246975/2²⁰]` isolates `+2^{1/4}`. -/

/-- `x⁴ − 2`; two real roots `±2^{1/4}`. -/
private def quartic : Hex.ZPoly := Hex.DensePoly.ofCoeffs #[(-2 : Int), 0, 0, 0, 1]

private theorem quartic_squarefree : Hex.ZPoly.SquareFreeRat quartic :=
  squareFreeRat_of_hasSquarefreeSturmChain _ (by decide)

/-- The refined, width-`2⁻²⁰` isolating interval for the positive root. -/
private def quarticIsoTight : Hex.RealRootIsolation quartic :=
  ⟨⟨Dyadic.ofInt 1246974 >>> (20 : Int), Dyadic.ofInt 1246975 >>> (20 : Int), by decide⟩,
    by decide⟩

private theorem quartic_isRoot_iff (x : ℝ) : (toPolyℝ quartic).IsRoot x ↔ x ^ 4 - 2 = 0 := by
  rw [Polynomial.IsRoot, eval_toPolyℝ, show quartic.size = 5 from by decide]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, quartic,
    Hex.DensePoly.coeff_ofCoeffs]
  norm_num
  constructor <;> intro h <;> linarith

private theorem quartic_root_pos_tight :
    ∃! x : ℝ, x ^ 4 - 2 = 0 ∧ (1246974 : ℝ) / 2 ^ 20 < x ∧ x ≤ 1246975 / 2 ^ 20 := by
  have h := quarticIsoTight.exists_unique_root quartic_squarefree
  simp only [quarticIsoTight, toReal_ofInt_shiftRight, quartic_isRoot_iff] at h
  convert h using 3
  all_goals norm_num

end Conformance
end HexRealRootsMathlib
