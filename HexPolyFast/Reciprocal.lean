/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFast.Reverse
public import HexTruncatedSeries.Inverse

public section

/-!
Plan-driven Newton reciprocals for fixed-precision truncated series.

Every bounded product in the Newton loop goes through `MulPlan.slice`.  The
agreement theorem below connects that executable polynomial kernel to the
existing `TSeries.mulUpTo` semantics.
-/

namespace Hex.DensePoly

universe u

attribute [local instance 1000] Lean.Grind.Semiring.ofNat

variable {R : Type u} [DecidableEq R] [Lean.Grind.CommRing R]

private theorem fold_diagonal_extend (p q : DensePoly R) (n d : Nat) :
    (List.range (p.size + d)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range p.size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      have hcoeff : p.coeff (p.size + d) = 0 :=
        coeff_eq_zero_of_size_le p (by omega)
      simp [diagonalMulCoeffTerm, hcoeff]
      grind

private theorem fold_diagonal_truncate (p q : DensePoly R) (n d : Nat) :
    (List.range (n + 1 + d)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      simp [diagonalMulCoeffTerm]
      grind

/-- A polynomial multiplication diagonal may always be normalized to the
canonical degree-sized range, independently of the left operand's support. -/
theorem diagonal_eq_degree_bound (p q : DensePoly R) (n : Nat) :
    (List.range p.size).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 =
      (List.range (n + 1)).foldl
        (fun acc i => acc + diagonalMulCoeffTerm p q n i) 0 := by
  by_cases hp : p.size ≤ n + 1
  · have hsum : p.size + (n + 1 - p.size) = n + 1 := by omega
    rw [← hsum]
    exact (fold_diagonal_extend p q n (n + 1 - p.size)).symm
  · have hsum : n + 1 + (p.size - (n + 1)) = p.size := by omega
    rw [← hsum]
    exact fold_diagonal_truncate p q n (p.size - (n + 1))

/-- Polynomial conversion preserves every represented product coefficient. -/
theorem coeff_polyOfSeries_mul {n : Nat} (a b : TSeries R n)
    (i : Nat) (hi : i < n) :
    (polyOfSeries a * polyOfSeries b).coeff i = (a * b).coeff i := by
  rw [DensePoly.coeff_mul, mulCoeffSum_eq_diagonal,
    diagonal_eq_degree_bound, TSeries.coeff_mul a b i hi]
  unfold TSeries.convCoeff
  apply List.foldl_add_congr
  intro j hj
  have hjle : j ≤ i := by
    have := List.mem_range.mp hj
    omega
  unfold diagonalMulCoeffTerm
  rw [ite_eq_right (by omega), coeff_polyOfSeries_of_lt,
    coeff_polyOfSeries_of_lt]
  all_goals omega

/-- Multiply two series through degree `m - 1` with a polynomial
multiplication plan. -/
def seriesMulUpTo (plan : MulPlan R) {n : Nat} (m : Nat)
    (a b : TSeries R n) : TSeries R n :=
  let p := mulLow plan m (polyOfSeries a) (polyOfSeries b)
  TSeries.ofFn fun i => p.coeff i

/-- Planned bounded series multiplication has exactly the established
`TSeries.mulUpTo` semantics. -/
theorem seriesMulUpTo_eq (plan : MulPlan R) {n : Nat} (m : Nat)
    (a b : TSeries R n) :
    seriesMulUpTo plan m a b = TSeries.mulUpTo m a b := by
  apply TSeries.ext
  intro i hi
  unfold seriesMulUpTo
  rw [TSeries.coeff_ofFn _ i hi, coeff_mulLow,
    TSeries.coeff_mulUpTo m a b i hi]
  split
  · rw [coeff_polyOfSeries_mul a b i hi]
  · rfl

/-- One Newton reciprocal update whose two bounded products both use the
supplied multiplication plan. -/
def reciprocalStep (plan : MulPlan R) {n : Nat} (g h : TSeries R n)
    (m : Nat) : TSeries R n :=
  seriesMulUpTo plan m h
    (TSeries.C (1 + 1) - seriesMulUpTo plan m g h)

/-- A planned Newton update agrees exactly with the reference series update. -/
theorem reciprocalStep_eq (plan : MulPlan R) {n : Nat}
    (g h : TSeries R n) (m : Nat) :
    reciprocalStep plan g h m = TSeries.invStep g h m := by
  unfold reciprocalStep TSeries.invStep
  rw [seriesMulUpTo_eq, seriesMulUpTo_eq]

/-- Newton reciprocal at the full represented precision.  Each doubling step
uses `plan.slice 0 k`; no schoolbook `TSeries` product is executed by this
definition. -/
def reciprocalWith (plan : MulPlan R) {n : Nat}
    (g : TSeries R n) (u : R) : TSeries R n :=
  TSeries.newton (reciprocalStep plan g) (TSeries.C u) (TSeries.steps n)

/-- The plan-driven reciprocal has the established truncated-series
semantics.  The inverse-witness hypothesis is intentionally not needed for
algorithmic agreement; it is needed by the defining inverse equation below. -/
theorem reciprocalWith_eq (plan : MulPlan R) {n : Nat}
    (g : TSeries R n) (u : R) :
    reciprocalWith plan g u = TSeries.invOfUnit g u := by
  have hstep : reciprocalStep plan g = TSeries.invStep g := by
    funext h m
    exact reciprocalStep_eq plan g h m
  unfold reciprocalWith TSeries.invOfUnit TSeries.invUpTo
  simp only [Nat.min_self, hstep]
  apply TSeries.ext
  intro i hi
  rw [TSeries.coeff_ofFn _ i hi, ite_eq_left hi]

/-- A planned reciprocal satisfies the multiplicative inverse equation when
the supplied constant coefficient really is an inverse. -/
theorem reciprocalWith_mul (plan : MulPlan R) {n : Nat}
    (g : TSeries R n) (u : R) (hu : g.coeff 0 * u = 1) :
    g * reciprocalWith plan g u = 1 := by
  rw [reciprocalWith_eq]
  exact TSeries.invOfUnit_mul g u hu

end Hex.DensePoly
