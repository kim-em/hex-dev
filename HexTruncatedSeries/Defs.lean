/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic

public section

/-!
The fixed-precision representation underlying `hex-truncated-series`.

A `TSeries R n` stores exactly the coefficients below precision `n`; trailing
zeros are data rather than a normalization condition.  Coefficient access is
total and reads as zero beyond the represented precision.  Tabulation and
equality deliberately use the kernel-reducible `HexBasic` vector helpers so
downstream `decide +kernel` computations continue through module boundaries.
-/

namespace Hex

universe u

/-- A power series over `R` truncated at precision `n`, represented by its
coefficients in ascending degree order. -/
structure TSeries (R : Type u) (n : Nat) where
  /-- The coefficients of `x^0` through `x^(n-1)`. -/
  coeffs : Vector R n

namespace TSeries

variable {R : Type u} {n : Nat}

/-- The coefficient of `x^i`, read as zero when `i` is beyond the precision. -/
@[expose]
def coeff [Zero R] (a : TSeries R n) (i : Nat) : R :=
  if h : i < n then a.coeffs[i] else 0

/-- Tabulate a truncated series from a total coefficient function. -/
@[expose]
def ofFn (f : Nat → R) : TSeries R n :=
  ⟨Hex.Vector.ofFn' fun i => f i.val⟩

/-- Tabulation stores the requested coefficient at every represented index. -/
@[simp, grind =]
theorem coeff_ofFn [Zero R] (f : Nat → R) (i : Nat) (hi : i < n) :
    (ofFn (n := n) f).coeff i = f i := by
  simp [coeff, ofFn, hi]

/-- Two truncated series are equal when all represented coefficients agree. -/
@[ext]
theorem ext [Zero R] {a b : TSeries R n}
    (h : ∀ i, i < n → a.coeff i = b.coeff i) : a = b := by
  cases a with
  | mk ac =>
      cases b with
      | mk bc =>
          congr 1
          apply Vector.ext
          intro i hi
          simpa [coeff, hi] using h i hi

/-- Kernel-reducible equality, routed through `HexBasic`'s vector equality. -/
instance [DecidableEq R] : DecidableEq (TSeries R n) := fun a b =>
  match h : decEq a.coeffs b.coeffs with
  | isTrue ht => isTrue (by cases a; cases b; cases ht; rfl)
  | isFalse hf => isFalse (by
      intro hab
      exact hf (congrArg TSeries.coeffs hab))

end TSeries
end Hex
