/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic

public section

/-!
The starting point of the subdivision: a single square, centred at the
origin, whose circumscribed region covers the Cauchy root bound of the
input polynomial. Every complex root of `p` lies strictly inside this
square, so refinement can begin from it.

The half-width is `2^{-prec}` with `prec := -(cauchyExp p)`, negative
whenever the root bound exceeds `1`; `cauchyExp` is pure integer
arithmetic on the coefficient magnitudes, with no floating point.
-/
namespace Hex

/-- Smallest `e : Nat` with `2^e ≥ 1 + max_{i<n} |aᵢ| / |aₙ|` (the Cauchy
    root bound): every complex root of `p` satisfies `|z| < 2^e`, so all
    roots lie in the square of half-width `2^e` about `0`. Pure integer
    arithmetic: with `L := |aₙ|` the leading magnitude and
    `M := max_{i<n} |aᵢ|` the largest non-leading magnitude, take
    `e := ceilLog2 ⌈(L + M) / L⌉ = ceilLog2 ((L + M + L - 1) / L)`. Junk
    `0` when `p` is the zero polynomial (no leading coefficient). -/
@[expose] def cauchyExp (p : ZPoly) : Nat :=
  let L := p.leadingCoeff.natAbs
  if L = 0 then 0
  else
    let M := (p.toArray.extract 0 (p.size - 1)).foldl
      (init := 0) fun acc a => Nat.max acc a.natAbs
    Hex.ceilLog2 ((L + M + L - 1) / L)

namespace Component

/-- The starting component: a single square centred at `0` covering the
    Cauchy root bound, with `candidateK = deg p`. Its half-width is
    `2^{-prec}` with `prec = -(cauchyExp p)`, so its closed square
    contains every complex root of `p`. -/
@[expose] def cauchy (p : ZPoly) (h : 0 < p.degree?.getD 0) : Component :=
  { squares := #[⟨0, 0, -(cauchyExp p : Int)⟩], candidateK := p.degree?.getD 0 }

end Component

end Hex
