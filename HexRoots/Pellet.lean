/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Taylor

public section

/-!
The Pellet witnesses of the complex root isolator: dyadic lower and upper
bounds `lo`/`hi` on the modulus of a Gaussian dyadic, the rational bounds
`181/128 < √2 < 1449/1024` on the circumscribed-disc factor, the
three-radius strong Pellet predicate `witness` with its `Decidable`
instance, and the certified cluster type `DyadicRootCluster` whose field
carries that witness.

With `(c₀, …, c_n)` the exact Taylor coefficients of `p` at the centre of a
square `s` (from `HexRoots.Taylor`) and `ρlo, ρhi` the dyadic bounds on the
circumscribed radius `2^{−s.prec}·√2`, one Pellet inequality reads

```
lo(c_k) · ρlo^k > Σ_{i ≠ k} hi(c_i) · ρhi^i
```

a strict comparison between two exact dyadics. Each `|c_i|` is replaced by
an exact dyadic on the safe side (`lo` below on the left, `hi` above on the
right), so the whole test is `Decidable` with no error budget. The
three-radius form checks this at the base radius and at 2× and 4× the base,
BSSY's condition for Newton readiness. The single-radius `T_0` variant
`rootFree` certifies the disc contains no root at all; it drives the
refinement discard, where certifying emptiness is what must be sound and
keeping a square is always safe.

Everything reachable from `witness`/`rootFree` is `@[expose]`, so the
kernel reduces the witnesses across module boundaries under `decide`; the
range folds below (rather than `for` loops or `Array.map`) are what make
that reduction go through.
-/
namespace Hex

namespace GaussDyadic

/-- `lo(c) = max(|Re c|, |Im c|)`: `lo(c) ≤ |c| ≤ √2·lo(c)`. -/
@[expose] def lo (z : GaussDyadic) : Dyadic :=
  Hex.Dyadic.max (Hex.Dyadic.abs z.1) (Hex.Dyadic.abs z.2)

/-- `hi(c) = |Re c| + |Im c|`: `|c| ≤ hi(c) ≤ √2·|c|`. -/
@[expose] def hi (z : GaussDyadic) : Dyadic :=
  Hex.Dyadic.abs z.1 + Hex.Dyadic.abs z.2

end GaussDyadic

/-- `181/128 < √2`. -/
@[expose] def sqrt2Lo : Dyadic := .ofIntWithPrec 181 7

/-- `√2 < 1449/1024`. -/
@[expose] def sqrt2Hi : Dyadic := .ofIntWithPrec 1449 10

/-- `(181/128)² < 2`, the defining inequality of `sqrt2Lo` (it reduces to
    `32761/16384 < 2`). -/
theorem sqrt2Lo_sq_lt_two : sqrt2Lo * sqrt2Lo < 2 := by decide

/-- `2 < (1449/1024)²`, the defining inequality of `sqrt2Hi` (it reduces to
    `2 < 2099601/1048576`). -/
theorem two_lt_sqrt2Hi_sq : 2 < sqrt2Hi * sqrt2Hi := by decide

/-- Dyadic lower bound `sqrt2Lo·2^{−prec}` for the square's circumscribed
    radius `2^{−prec}·√2`. -/
@[expose] def DyadicSquare.radiusLo (s : DyadicSquare) : Dyadic := .ofIntWithPrec 181 (s.prec + 7)

/-- Dyadic upper bound `sqrt2Hi·2^{−prec}` for the square's circumscribed
    radius `2^{−prec}·√2`. -/
@[expose] def DyadicSquare.radiusHi (s : DyadicSquare) : Dyadic := .ofIntWithPrec 1449 (s.prec + 10)

/-- One Pellet inequality: `lo(cs[k])·rlo^k > Σ_{i ≠ k} hi(cs[i])·rhi^i`
    (strict), with `cs` the exact Taylor coefficients. The right side is a
    single fold over `cs` carrying the running power `rhi^i`, skipping the
    `i = k` term. Returns `false` when `k ≥ cs.size` (no such coefficient). -/
@[expose] def pelletAt (cs : Array GaussDyadic) (k : Nat) (rlo rhi : Dyadic) : Bool :=
  if k < cs.size then
    let lhs := GaussDyadic.lo (cs.getD k (0, 0)) * rlo ^ k
    let rhs :=
      ((List.range cs.size).foldl (init := ((0 : Dyadic), (1 : Dyadic)))
        fun acc i =>
          let acc' := if i = k then acc.1 else acc.1 + GaussDyadic.hi (cs.getD i (0, 0)) * acc.2
          (acc', acc.2 * rhi)).1
    decide (rhs < lhs)
  else
    false

/-- Three-radius strong Pellet check for `k` roots (with multiplicity) in
    the circumscribed disc of `s`: the exact Taylor coefficients of `p` at
    `s.center`, tested by `pelletAt` at the base radius bounds and at 2× and
    4× the base radius (the radius bounds shifted left by 1 and 2). This is
    BSSY's Newton-readiness condition. -/
@[expose] def witnessCheck (p : ZPoly) (s : DyadicSquare) (k : Nat) : Bool :=
  let cs := taylor p s.center
  pelletAt cs k s.radiusLo s.radiusHi
    && pelletAt cs k (s.radiusLo <<< (1 : Int)) (s.radiusHi <<< (1 : Int))
    && pelletAt cs k (s.radiusLo <<< (2 : Int)) (s.radiusHi <<< (2 : Int))

/-- Strong Pellet witness: with `(c₀, …, c_n)` the exact Taylor
    coefficients of `p` at the centre of `s`, and `ρlo, ρhi` the dyadic
    bounds on the circumscribed radius `2^{−s.prec}·√2`, the inequality

      `lo(c_k) · ρlo^k > Σ_{i ≠ k} hi(c_i) · ρhi^i`

    holds at the base radius and at 2 and 4 times the base radius.
    Implies (Mathlib companion): `p` has exactly `k` roots, with
    multiplicity, in each of the three discs. -/
@[expose] def witness (p : ZPoly) (s : DyadicSquare) (k : Nat) : Prop := witnessCheck p s k = true

instance {p : ZPoly} {s : DyadicSquare} {k : Nat} : Decidable (witness p s k) :=
  inferInstanceAs (Decidable (_ = true))

/-- Single-radius `T_0` exclusion: the circumscribed disc of `s`
    certifiably contains no root of `p`, i.e. `lo(c₀) > Σ_{i ≥ 1} hi(c_i)·ρhi^i`
    (the `rlo^0 = 1` power makes the base radius bound `rlo` unused). This
    fires more often than the three-radius `witness _ _ 0`; discarding a
    square during refinement needs certification while keeping one is always
    sound, so refinement uses this. -/
@[expose] def rootFree (p : ZPoly) (s : DyadicSquare) : Bool :=
  pelletAt (taylor p s.center) 0 s.radiusLo s.radiusHi

/-! ### Ball geometry and ball evaluation

`DyadicComplexBall` consumers (numerical evaluation in this library's
future callers, and `hex-number-field`'s root disambiguation) need the
disc-to-ball view of a square, a sound enclosure of `p` on a square's
disc, and the exclusion and intersection tests on balls. The radius
conventions here reuse the audited `radiusHi` upper bound, so callers
never re-derive the `√2` bookkeeping. -/

/-- The circumscribed disc of `s` as a ball, with the dyadic upper-bound
    radius `radiusHi` (`≥` the true radius `2^{−prec}·√2`). -/
@[expose] def DyadicSquare.toBall (s : DyadicSquare) : DyadicComplexBall :=
  ⟨s.re, s.im, s.radiusHi⟩

/-- A ball containing `p(z)` for every `z` in the circumscribed disc of
    `s`: centred at the exact value `p(centre) = c₀`, with radius
    `Σ_{i ≥ 1} hi(cᵢ)·radiusHi^i ≥ |p(z) − p(centre)|` by the triangle
    inequality on the Taylor expansion. `rootFree` is the corollary
    `lo(c₀) > radius` (kept separate so the audited `pelletAt` shape is
    unchanged). -/
@[expose] def evalBall (p : ZPoly) (s : DyadicSquare) : DyadicComplexBall :=
  let cs := taylor p s.center
  let c0 := cs.getD 0 (0, 0)
  let radius :=
    ((List.range cs.size).foldl (init := ((0 : Dyadic), (1 : Dyadic)))
      fun acc i =>
        if 1 ≤ i then
          (acc.1 + GaussDyadic.hi (cs.getD i (0, 0)) * (acc.2 * s.radiusHi),
           acc.2 * s.radiusHi)
        else acc).1
  ⟨c0.1, c0.2, radius⟩

/-- The ball certifiably excludes `0`: `radius < lo(centre) ≤ |centre|`,
    an exact dyadic comparison. The sound direction for "this value is
    certainly nonzero"; failing this test means only that `0` could not
    be excluded. -/
@[expose] def DyadicComplexBall.excludesZero (b : DyadicComplexBall) : Bool :=
  decide (b.radius < Hex.Dyadic.max (Hex.Dyadic.abs b.re) (Hex.Dyadic.abs b.im))

/-- The closed balls intersect: squared centre distance at most the
    squared radius sum, all exact dyadics. -/
@[expose] def DyadicComplexBall.meets (b₁ b₂ : DyadicComplexBall) : Bool :=
  let rs := b₁.radius + b₂.radius
  decide (GaussDyadic.distSq (b₁.re, b₁.im) (b₂.re, b₂.im) ≤ rs * rs)

/-- The ball meets the circumscribed disc of `s` (conservative: uses the
    `radiusHi` upper bound for the disc radius, so a `false` certifies
    disjointness from the true disc as well). -/
@[expose] def DyadicSquare.meetsBall (s : DyadicSquare) (b : DyadicComplexBall) : Bool :=
  DyadicComplexBall.meets s.toBall b

/-- A certified cluster: an edge-connected set of grid squares at a
    common `prec`, whose enclosing disc contains exactly `k` roots
    with multiplicity. The component squares are the data that
    *refinement* operates on; subdividing the enclosing square
    instead would stall (it can equal the parent square when a root
    sits on a grid line, even as the component squares themselves
    shrink). The Pellet certificate, by contrast, is attached to the
    circumscribed disc of `encSquare squares`. This is an *output*
    type; the refinement worklist holds uncertified `Component`
    values. -/
structure DyadicRootCluster (p : ZPoly) where
  /-- The component's grid squares: nonempty, common `prec`, edge-connected. -/
  squares : Array DyadicSquare
  /-- The number of roots, counted with multiplicity, in the enclosing disc. -/
  k : Nat
  /-- A cluster carries at least one root. -/
  k_pos : 0 < k
  /-- The strong Pellet certificate on the enclosing square's disc. -/
  witness : Hex.witness p (encSquare squares) k

end Hex
