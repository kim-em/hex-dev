/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Taylor

public section

/-!
The speculative Newton step for complex root refinement. From the centre
of a square `s`, one Newton (or `k`-order cluster) step produces a
recentred, much smaller candidate square at

```
x' = x − k · c₀ / c₁ ,
```

where `c₀, c₁` are the first two exact Gaussian-dyadic Taylor coefficients
of `p` at the centre. The Gaussian inversion `1/c₁ = conj(c₁)/|c₁|²` uses
one real reciprocal `Dyadic.invAtPrec (|c₁|²)`, reused by both centre
components, rather than two separate divisions.

The step is purely speculative: it checks no "Newton readiness"
precondition. The caller must re-certify the result and apply the coverage
guard (implemented in `Bisection.lean`); a step that fails to certify is
discarded and subdivision proceeds. Soundness never depends on the
precision choices here, only the success rate does.
-/
namespace Hex

/-- Speculative Newton step `x' = x − k·c₀/c₁` from the centre of `s`,
    returning the recentred, much smaller square at
    `prec' = max (s.prec + 2) (2·s.prec)`. `k = 1` is the atom form; general
    `k` is the `k`-order cluster step (BSSY §5). Purely speculative: the
    caller must re-certify and apply the coverage guard. Degree `< 1`
    (`cs.size < 2`) returns `s` unchanged; `c₁ = 0` gives `1/|c₁|² = 0`, so
    the centre is returned unchanged (`x' = x`) at the finer `prec'`. Either
    way the degenerate result is rejected by the re-check. -/
@[expose] def newtonSquare (p : ZPoly) (s : DyadicSquare) (k : Nat) : DyadicSquare :=
  let cs := taylor p s.center
  if cs.size < 2 then s else
  let c0 := cs.getD 0 (0, 0)
  let c1 := cs.getD 1 (0, 0)
  let d  := GaussDyadic.normSq c1                        -- |c₁|², exact
  let t  := GaussDyadic.mul (GaussDyadic.ofInt (k : Int))
              (GaussDyadic.mul c0 (GaussDyadic.conj c1)) -- k·c₀·conj(c₁), exact
  let prec' := max (s.prec + 2) (2 * s.prec)
  -- Magnitude bound `|t| ≤ tb := |Re t| + |Im t|`, inlined here rather than
  -- pulled from `GaussDyadic.hi` (which lives in the sibling `Pellet.lean`,
  -- deliberately not imported).
  let tb := Hex.Dyadic.abs t.1 + Hex.Dyadic.abs t.2
  let q := prec' + 2 + max 0 (Hex.Dyadic.ceilLog2 tb)
  let inv := d.invAtPrec q                               -- ONE real reciprocal 1/|c₁|²
  -- `invAtPrec` floors at precision `q` (error `< 2^{−q}` toward zero), so each
  -- centre component's reciprocal error is `< |tᵢ|·2^{−q} ≤ tb·2^{−q} ≤ 2^{−(prec'+2)}`
  -- (strictness from the reciprocal rounding error). The final `roundDown` at
  -- `prec' + 3` adds at most `2^{−(prec'+3)}` per component, for a total under
  -- `3·2^{−(prec'+3)} < 2^{−(prec'+1)}`, half of the new half-width `2^{−prec'}`: a genuinely converged Newton
  -- step keeps the root inside the new square. The rounding also pins the
  -- centre's bit-length to about `prec' + 3` plus its magnitude, keeping every
  -- downstream Taylor shift on `B`-bit values per the complexity contract;
  -- without it, exact recentring compounds (each jump multiplies centre bits
  -- by about `2·deg p`), which measured as 30k-digit centres by the fourth
  -- jump on a degree-4 input. Certification never trusts the centre's
  -- provenance, so rounding is harmless to soundness. `prec' = max (prec+2) (2·prec)`
  -- gives at least a quarter-size square always (also for `prec ≤ 0`) and
  -- precision doubling once `prec ≥ 2`; only success rate, never soundness,
  -- depends on this choice. `Dyadic.invAtPrec` returns `0` for a zero argument
  -- (`Init.Data.Dyadic.Inv.lean`: the `.zero` case), so `c₁ = 0` yields
  -- `inv = 0` and `x' = x` harmlessly.
  { re := (s.re - t.1 * inv).roundDown (prec' + 3),
    im := (s.im - t.2 * inv).roundDown (prec' + 3),
    prec := prec' }

/-- The square concentric with `s`, one level coarser (half-width doubled).
    The Newton-Kantorovich certification convention tests and stores this. -/
@[expose] def DyadicSquare.doubled (s : DyadicSquare) : DyadicSquare :=
  { s with prec := s.prec - 1 }

end Hex
