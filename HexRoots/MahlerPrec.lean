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
