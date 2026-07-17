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

namespace GaussDyadic

/-- A natural multiple of a Gaussian dyadic. -/
@[expose] def nsmul (n : Nat) (w : GaussDyadic) : GaussDyadic :=
  mul (ofInt n) w

/-- A natural power of a Gaussian dyadic. -/
@[expose] def pow (z : GaussDyadic) : Nat → GaussDyadic
  | 0 => ofInt 1
  | n + 1 => mul (pow z n) z

end GaussDyadic

/-- The closed-form coefficient of `X^k` in the Taylor shift of `p` by `z`.
    The range index `r` represents the source coefficient at `j = k + r`. -/
@[expose] def taylorCoeff (p : ZPoly) (z : GaussDyadic) (k : Nat) : GaussDyadic :=
  (List.range (p.size - k)).foldl (init := (0, 0)) fun acc r =>
    GaussDyadic.add acc
      (GaussDyadic.nsmul (Hex.Nat.binom (k + r) k)
        (GaussDyadic.mul (GaussDyadic.ofInt (p.coeff (k + r))) (GaussDyadic.pow z r)))

/-- Proof-facing Taylor expansion. Its coefficients are the closed binomial
    sums; compiled callers are redirected to the quadratic implementation. -/
@[expose] def taylorSpec (p : ZPoly) (z : GaussDyadic) : Array GaussDyadic :=
  ((List.range p.size).map fun k => taylorCoeff p z k).toArray

/-- The audited quadratic in-place implementation of `taylor`. -/
private def taylorImpl (p : ZPoly) (z : GaussDyadic) : Array GaussDyadic :=
  let n := p.size
  let a₀ : Array GaussDyadic :=
    ((List.range n).map fun i => GaussDyadic.ofInt (p.coeff i)).toArray
  (List.range n).foldl (init := a₀) fun a k =>
    (List.range ((n - 1) - k)).foldl (init := a) fun a jr =>
      let j := n - 2 - jr
      a.setIfInBounds j
        (GaussDyadic.add (a.getD j (0, 0)) (GaussDyadic.mul z (a.getD (j + 1) (0, 0))))

/-- Exact Taylor coefficients of `p` at the Gaussian-dyadic point `z`:
    returns `#[c₀, …, c_n]` with `p(X + z) = Σ cₖ Xᵏ`, where
    `cₖ = Σ_{j ≥ k} binomial(j, k) · aⱼ · z^{j−k}` exactly. The result has
    size `p.size` (empty for the zero polynomial, a single cast coefficient
    for a nonzero constant). Computed by repeated synthetic division, using
    only exact Gaussian-dyadic additions and multiplications in compiled code;
    its logical body is `taylorSpec`, exposing the binomial sum to proofs. -/
@[expose, implemented_by taylorImpl] def taylor (p : ZPoly) (z : GaussDyadic) : Array GaussDyadic :=
  taylorSpec p z

/-- The Taylor expansion has one coefficient per stored coefficient of `p`:
    its proof-facing array is built over `List.range p.size`. -/
theorem taylor_size (p : ZPoly) (z : GaussDyadic) : (taylor p z).size = p.size := by
  simp [taylor, taylorSpec]

/-- Characterization of a Taylor coefficient as the finite binomial sum
    `Σ_r binom(k+r,k) · a_(k+r) · z^r`. -/
theorem taylor_getD (p : ZPoly) (z : GaussDyadic) (k : Nat) :
    (taylor p z).getD k (0, 0) =
      if k < p.size then taylorCoeff p z k else (0, 0) := by
  by_cases h : k < p.size
  · simp [taylor, taylorSpec, h]
  · simp [taylor, taylorSpec, h]

/-- In-bounds form of `taylor_getD`, convenient for companion proofs. -/
theorem taylor_getD_of_lt (p : ZPoly) (z : GaussDyadic) (k : Nat) (hk : k < p.size) :
    (taylor p z).getD k (0, 0) = taylorCoeff p z k := by
  simpa [hk] using taylor_getD p z k

end Hex
