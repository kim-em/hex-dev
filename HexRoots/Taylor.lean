/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic

public section

/-!
Exact Gaussian-dyadic Taylor expansion of an integer polynomial `p` at a
Gaussian-dyadic centre `z`. The result `#[c₀, …, c_n]` collects the
coefficients of `p(X + z) = Σ cₖ Xᵏ`, where

```
cₖ = Σ_{j ≥ k} binomial(j, k) · aⱼ · z^{j−k}
```

is computed *exactly* over `Dyadic[i]`, each `cₖ` a Gaussian dyadic. No
binomial coefficients are materialised: the expansion is produced by
repeated synthetic division (Horner passes) in a single mutable array,
`O(n²)` exact Gaussian-dyadic operations. This is the dominant cost of
every witness check in the library.
-/
namespace Hex

/-- Exact Taylor coefficients of `p` at the Gaussian-dyadic point `z`:
    returns `#[c₀, …, c_n]` with `p(X + z) = Σ cₖ Xᵏ`, where
    `cₖ = Σ_{j ≥ k} binomial(j, k) · aⱼ · z^{j−k}` exactly. The result has
    size `p.size` (empty for the zero polynomial, a single cast coefficient
    for a nonzero constant). Computed by repeated synthetic division, using
    only exact Gaussian-dyadic additions and multiplications. -/
@[expose] def taylor (p : ZPoly) (z : GaussDyadic) : Array GaussDyadic :=
  let n := p.size
  -- The single mutable array: initially the integer coefficients cast into
  -- `GaussDyadic`, then rewritten in place by the synthetic-division passes.
  let a₀ : Array GaussDyadic :=
    ((List.range n).map fun i => GaussDyadic.ofInt (p.coeff i)).toArray
  -- Pass `k` finalises `a[k]`: after it, `a[k]` is the Taylor coefficient `cₖ`.
  -- Pass `k`'s inner loop runs `j` from `n − 2` down to `k` (as `j = n − 2 − jr`
  -- for `jr` in `[0, (n−1)−k)`), applying one synthetic-division step
  -- `a[j] := a[j] + z·a[j+1]`. For `n ≤ 1` both loops are empty (`List.range n`
  -- is `[]` or `[0]` and the inner range `List.range ((n−1)−k)` is `[]`), so the
  -- result is just the cast coefficients. For `k = n − 1` the inner range is
  -- empty (`Nat` subtraction gives `0`), a no-op.
  (List.range n).foldl (init := a₀) fun a k =>
    (List.range ((n - 1) - k)).foldl (init := a) fun a jr =>
      let j := n - 2 - jr
      a.setIfInBounds j
        (GaussDyadic.add (a.getD j (0, 0)) (GaussDyadic.mul z (a.getD (j + 1) (0, 0))))

/-- A `List.foldl` whose step function preserves array size preserves the
    size of the accumulator. Used to see through the synthetic-division loop
    in `taylor`, whose only mutation is `Array.setIfInBounds`. -/
private theorem size_foldl {β : Type _} {f : Array GaussDyadic → β → Array GaussDyadic}
    (hf : ∀ b x, (f b x).size = b.size) (l : List β) (a : Array GaussDyadic) :
    (l.foldl f a).size = a.size := by
  induction l generalizing a with
  | nil => rfl
  | cons _ tl ih => simp only [List.foldl_cons, ih, hf]

/-- The Taylor expansion has one coefficient per stored coefficient of `p`:
    the synthetic-division passes only overwrite entries of the initial
    length-`p.size` array, never resize it. -/
theorem taylor_size (p : ZPoly) (z : GaussDyadic) : (taylor p z).size = p.size := by
  simp only [taylor]
  rw [size_foldl (fun b x => size_foldl (fun _ _ => Array.size_setIfInBounds ..) _ b)]
  simp

end Hex
