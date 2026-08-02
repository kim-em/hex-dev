/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic

public section

/-!
The closed-form separation precision `mahlerPrec` and the completeness
depth `separationDepth`.

For squarefree `p ∈ ℤ[x]` of degree `n`, the Mahler separation bound
gives
```
sep(p) := min_{i ≠ j} |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
```
where `M(p)` is the Mahler measure. `mahlerPrec p` is a precision at
which the circumscribed-disc radius `2^{−m}·√2` is strictly below
`sep(p)/4`; since `√2 < 1449/1024`, it suffices that
```
2^{−m} · 1449/1024 < sep(p) / 4.
```

The derivation uses only integer arithmetic and never materialises the
product `N` below:

* Combine the Mahler bound with `|disc p| ≥ 1` (the discriminant of a
  squarefree integer polynomial is a nonzero integer) and Landau's
  `M(p) ≤ √(n+1) · A` with `A := ‖p‖∞ = coeffAbsMax p`, then drop the
  `√3 ≥ 1` factor:
  ```
  sep(p) ≥ n^{−(n+2)/2} · ((n+1)·A²)^{−(n−1)/2}.
  ```
* Since `1449/1024 < 2`, the target `2^{−m} · 1449/1024 < sep(p)/4`
  follows (with the strict `< 2` supplying overall strictness) from
  ```
  2^{3−m} ≤ n^{−(n+2)/2} · ((n+1)·A²)^{−(n−1)/2},
  ```
  which, squared, is
  ```
  4^{m−3} ≥ N := n^{n+2} · (n+1)^{n−1} · A^{2(n−1)}.
  ```
* Bounding `log₂ N` by
  ```
  T := (n+2)·ceilLog2 n + (n−1)·ceilLog2 (n+1) + 2·(n−1)·ceilLog2 A
  ```
  gives `log₂ N ≤ T`, so `m := 3 + ⌈T/2⌉` satisfies `2m − 6 ≥ T ≥ log₂ N`,
  i.e. `4^{m−3} ≥ N`. This is the value returned.

The Mahler bound concerns *distinct* roots, so the formula is meaningful
even for non-squarefree `p`: for the squarefree part `p_sf` one has
`M(p_sf) ≤ M(p)` and `|disc p_sf| ≥ 1`, so the same closed form applies.
No discriminant is computed at runtime; only the constant lower bound
`|disc p| ≥ 1` is used. The Mathlib companion certifies this derivation.

The whole computation is `O(n · log ‖p‖∞)` integer operations. On
degenerate inputs (`n = 0`, `n = 1`, or `A = 0`) the Nat subtractions
`n − 1` truncate to `0` and `ceilLog2`'s junk-`0` branch fires, so every
term is harmless and the results are small totals.
-/
namespace Hex

namespace ZPoly

/-- `‖p‖∞`: the maximum absolute value of the coefficients of `p`, i.e.
    `max_i |pᵢ|`. Folds `Nat.max` over `Int.natAbs` of the stored
    coefficients; the zero polynomial has none, so it returns `0`. -/
@[expose] def coeffAbsMax (p : ZPoly) : Nat :=
  (List.range p.size).foldl (fun acc i => Nat.max acc (p.coeff i).natAbs) 0

/-- Reflection in the origin preserves coefficient height. -/
@[simp] theorem coeffAbsMax_dilate_neg_one (p : ZPoly) :
    coeffAbsMax (p.dilate (-1)) = coeffAbsMax p := by
  unfold coeffAbsMax
  rw [ZPoly.size_dilate_neg_one]
  have hfold (indices : List Nat) (acc : Nat) :
      indices.foldl
          (fun total i => Nat.max total ((p.dilate (-1)).coeff i).natAbs) acc =
        indices.foldl (fun total i => Nat.max total (p.coeff i).natAbs) acc := by
    induction indices generalizing acc with
    | nil => rfl
    | cons n indices ih =>
        simp only [List.foldl_cons]
        have habs : ((p.dilate (-1)).coeff n).natAbs = (p.coeff n).natAbs := by
          rw [ZPoly.coeff_dilate, Int.natAbs_mul, Int.natAbs_pow]
          rw [show (-1 : Int).natAbs = 1 by decide, Nat.one_pow, Nat.one_mul]
        rw [habs]
        exact ih _
  exact hfold (List.range p.size) 0

/-- Multiplication by `-1` preserves coefficient height. -/
@[simp] theorem coeffAbsMax_scale_neg_one (p : ZPoly) :
    coeffAbsMax (DensePoly.scale (-1) p) = coeffAbsMax p := by
  unfold coeffAbsMax
  rw [ZPoly.scale_size_of_ne_zero (-1 : Int) p (by decide)]
  have hfold (indices : List Nat) (acc : Nat) :
      indices.foldl (fun total i =>
          Nat.max total ((DensePoly.scale (-1) p).coeff i).natAbs) acc =
        indices.foldl (fun total i => Nat.max total (p.coeff i).natAbs) acc := by
    induction indices generalizing acc with
    | nil => rfl
    | cons n indices ih =>
        simp only [List.foldl_cons]
        have habs : ((DensePoly.scale (-1) p).coeff n).natAbs =
            (p.coeff n).natAbs := by
          rw [DensePoly.coeff_scale (R := Int) (-1) p n (Int.mul_zero _),
            Int.natAbs_mul]
          rw [show (-1 : Int).natAbs = 1 by decide, Nat.one_mul]
        rw [habs]
        exact ih _
  exact hfold (List.range p.size) 0

/-- Primitive sign normalization preserves coefficient height. -/
@[simp] theorem coeffAbsMax_normalizePrimitiveSign (p : ZPoly) :
    coeffAbsMax (p.normalizePrimitiveSign) = coeffAbsMax p := by
  unfold normalizePrimitiveSign
  split
  · exact coeffAbsMax_scale_neg_one p
  · rfl

end ZPoly

/-- Precision at which the circumscribed-disc radius `2^{−m}·√2` is
    strictly below `sep(p)/4` (derivation in the module docstring). Pure
    integer arithmetic in `O(n · log ‖p‖∞)`.

    On degenerate inputs the Nat subtractions `n − 1` truncate to `0` and
    `ceilLog2`'s junk-`0` branch handles `n ≤ 1` and `a = 0`, so the value
    is a small harmless total (`3` for `n ≤ 1`). -/
@[expose] def mahlerPrec (p : ZPoly) : Nat :=
  let n := p.degree?.getD 0
  let a := ZPoly.coeffAbsMax p
  let t := (n + 2) * ceilLog2 n + (n - 1) * ceilLog2 (n + 1) + 2 * (n - 1) * ceilLog2 a
  3 + (t + 1) / 2

/-- The fixed slack added to `mahlerPrec` in `separationDepth`: one level
    for the factor-2 witness slack, at most two for the enclosing square
    of a multi-square component, one for the circumscribed `√2`, and
    margin. -/
@[expose] def sepSlack : Nat := 8

/-- Depth at which the completeness analysis says every Pellet witness
    certifies. Past `mahlerPrec p` each component's disc contains at most
    one distinct root; the `ceilLog2 (max 2 (deg p))` term buys the
    degree-dependent isolation ratio the witness needs (one doubling per
    level), and `sepSlack` covers the fixed factors. It is the depth
    bound used by `stopDepth`. -/
@[expose] def separationDepth (p : ZPoly) : Nat :=
  mahlerPrec p + ceilLog2 (Nat.max 2 (p.degree?.getD 0)) + sepSlack

end Hex
