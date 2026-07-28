/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.SoftPellet

public section

/-!
The Pellet witnesses of the complex root isolator: exact dyadic lower and
upper bounds `lo`/`hi` on a Gaussian-dyadic modulus, the rational bounds
`181/128 < √2 < 1449/1024` on the circumscribed-disc factor, the
three-radius strong Pellet predicate `witness` with its `Decidable` instance,
and the certified cluster type `DyadicRootCluster` whose field carries that
witness. `HexRoots.SoftPellet` supplies the bounded-precision coefficient-ball
and Graeffe front end; the exact Taylor kernel here remains its fallback.

With `(c₀, …, c_n)` the exact Taylor coefficients of `p` at the centre of a
square `s` (from `HexRoots.Taylor`) and `ρlo, ρhi` the dyadic bounds on the
circumscribed radius `2^{−s.prec}·√2`, one Pellet inequality reads

```
lo(c_k) · ρlo^k > Σ_{i ≠ k} hi(c_i) · ρhi^i
```

a strict comparison between two exact dyadics. Each `|c_i|` is replaced by
an exact dyadic on the safe side (`lo` below on the left, `hi` above on the
right), so the whole test is `Decidable` with no floating-point trust. A soft
success proves this same predicate; a soft failure falls through to the exact
comparison. The
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

namespace TaylorShift

/-- Three-radius strong Pellet check from an already-computed Taylor shift.
    Keeping this coefficient-level kernel separate lets a certifier test every
    candidate root count at one centre without repeating the quadratic Taylor
    shift. -/
@[expose] def witnessCheck {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat) : Bool :=
  pelletAt shift.coeffs k s.radiusLo s.radiusHi
    && pelletAt shift.coeffs k (s.radiusLo <<< (1 : Int)) (s.radiusHi <<< (1 : Int))
    && pelletAt shift.coeffs k (s.radiusLo <<< (2 : Int)) (s.radiusHi <<< (2 : Int))

end TaylorShift

namespace TaylorShift

/-- At shallow centre precision, try the cached exact Taylor check first; this
preserves its small constant on easy canonical inputs. At deep precision, try
soft Graeffe first so successful witnesses avoid evaluating the increasingly
large exact coefficients. -/
@[expose] def combinedWitnessCheck {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat) : Bool :=
  if s.prec < 32 then
    TaylorShift.witnessCheck s shift k || shift.softWitnessCheck s k
  else
    shift.softWitnessCheck s k || TaylorShift.witnessCheck s shift k

end TaylorShift

/-- Three-radius strong Pellet check for `k` roots (with multiplicity) in the
    circumscribed disc of `s`. It accepts either the exact Taylor comparison at
    the base, doubled, and quadrupled radii, or an outward-rounded comparison
    after transporting the polynomial and all three radii through Graeffe
    root-squaring. Both routes imply BSSY's three-radius root-count condition. -/
@[expose] def witnessCheck (p : ZPoly) (s : DyadicSquare) (k : Nat) : Bool :=
  TaylorShift.combinedWitnessCheck s (TaylorShift.compute p s.center) k

/-- The centre-indexed combined kernel is exactly the public polynomial
    witness check. -/
@[simp] theorem TaylorShift.combinedWitnessCheck_eq {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat) :
    TaylorShift.combinedWitnessCheck s shift k = _root_.Hex.witnessCheck p s k := by
  by_cases hprec : s.prec < 32 <;>
    simp [TaylorShift.combinedWitnessCheck, _root_.Hex.witnessCheck,
      TaylorShift.witnessCheck, hprec, shift.valid,
      (TaylorShift.compute p s.center).valid,
      TaylorShift.softWitnessCheck_eq s shift k,
      TaylorShift.softWitnessCheck_eq s (TaylorShift.compute p s.center) k]

/-- A root-count witness cannot select a coefficient outside the polynomial. -/
theorem witnessCheck_false {p : ZPoly} {s : DyadicSquare} {k : Nat}
    (h : p.size ≤ k) : witnessCheck p s k = false := by
  have hexact :
      TaylorShift.witnessCheck s (TaylorShift.compute p s.center) k = false := by
    simp [TaylorShift.witnessCheck, pelletAt, TaylorShift.compute, taylor_size,
      Nat.not_lt.mpr h]
  have hsoft :
      (TaylorShift.compute p s.center).softWitnessCheck s k = false := by
    simpa [softWitnessCheck] using softWitnessCheck_false (p := p) (s := s) h
  simp [witnessCheck, TaylorShift.combinedWitnessCheck, hexact, hsoft]

/-- A successful exact centre-indexed check implies the public disjunctive
    witness check. -/
theorem TaylorShift.witnessCheck_implies {p : ZPoly} (s : DyadicSquare)
    (shift : TaylorShift p s.center) (k : Nat)
    (h : TaylorShift.witnessCheck s shift k = true) :
    _root_.Hex.witnessCheck p s k = true := by
  rw [← TaylorShift.combinedWitnessCheck_eq s shift k]
  simp [TaylorShift.combinedWitnessCheck, h]

/-- Strong Pellet witness accepted by the exact or outward-rounded Graeffe
    route. Implies (Mathlib companion): `p` has exactly `k` roots, with
    multiplicity, in the circumscribed disc of `s` and in its doubled and
    quadrupled concentric discs, with no roots on their boundaries. -/
@[expose] def witness (p : ZPoly) (s : DyadicSquare) (k : Nat) : Prop := witnessCheck p s k = true

instance {p : ZPoly} {s : DyadicSquare} {k : Nat} : Decidable (witness p s k) :=
  inferInstanceAs (Decidable (_ = true))

/-- Exact single-radius `T_0` exclusion: the circumscribed disc of `s`
    certifiably contains no root of `p`, i.e. `lo(c₀) > Σ_{i ≥ 1} hi(c_i)·ρhi^i`
    (the `rlo^0 = 1` power makes the base radius bound `rlo` unused). This
    fires more often than the three-radius `witness _ _ 0`; discarding a
    square during refinement needs certification while keeping one is always
    sound, so refinement uses this. -/
@[expose] def exactRootFree (p : ZPoly) (s : DyadicSquare) : Bool :=
  pelletAt (taylor p s.center) 0 s.radiusLo s.radiusHi

/-- Graeffe `T₀` discard with exact fallback.  Shallow centres seed the
coefficient balls from one exact Taylor shift; large centres use the fully
soft constructor whose mantissas are independent of centre bit-length. -/
@[expose] def rootFree (p : ZPoly) (s : DyadicSquare) : Bool :=
  if 32 ≤ p.size then
    if s.prec < 32 then
      let ks := (Array.range p.size).toList
      match softSeededRootCount? p s ks 64 with
      | some 0 => true
      | _ => exactRootFree p s
    else softRootFree p s || exactRootFree p s
  else exactRootFree p s

/-- Exact exclusion remains a sufficient result for the combined filter. -/
theorem exactRootFree_implies_rootFree {p : ZPoly} {s : DyadicSquare}
    (h : exactRootFree p s = true) : rootFree p s = true := by
  unfold rootFree
  split
  · split
    · dsimp only
      generalize softSeededRootCount? p s (Array.range p.size).toList 64 = result
      cases result with
      | none => simp [h]
      | some k => cases k <;> simp [h]
    · simp [h]
  · exact h

/-! # Ball geometry and ball evaluation

`DyadicComplexBall` consumers, including numerical evaluation and
`hex-number-field` root disambiguation, use the
disc-to-ball view of a square, a sound enclosure of `p` on a square's
disc, and the exclusion and intersection tests on balls. The radius
conventions here reuse the audited `radiusHi` upper bound, so callers
never re-derive the `√2` bookkeeping. -/

/-- The circumscribed disc of `s` as a ball, with the dyadic upper-bound
    radius `radiusHi` (`≥` the true radius `2^{−prec}·√2`). -/
@[expose] def DyadicSquare.toBall (s : DyadicSquare) : DyadicComplexBall :=
  ⟨s.re, s.im, s.radiusHi⟩

namespace DyadicComplexBall

/-- The exact zero complex ball. -/
@[expose]
def zero : DyadicComplexBall := ⟨0, 0, 0⟩

/-- Minkowski sum of two closed dyadic complex balls. -/
@[expose]
def add (a b : DyadicComplexBall) : DyadicComplexBall :=
  ⟨a.re + b.re, a.im + b.im, a.radius + b.radius⟩

/-- Product enclosure for two closed dyadic complex balls. -/
@[expose]
def mul (a b : DyadicComplexBall) : DyadicComplexBall :=
  let ac : GaussDyadic := (a.re, a.im)
  let bc : GaussDyadic := (b.re, b.im)
  let center := GaussDyadic.mul ac bc
  let radius :=
    GaussDyadic.hi ac * b.radius + GaussDyadic.hi bc * a.radius +
      a.radius * b.radius
  ⟨center.1, center.2, radius⟩

/-- Enclose a rational number by a real-centred dyadic complex ball. Exact
dyadic rationals receive radius zero; otherwise one ulp encloses the downward
rounding error. At nonnegative precision the denominator test avoids
materializing and normalizing a large intermediate rational. -/
@[expose]
def ofRat (q : Rat) (prec : Int) : DyadicComplexBall :=
  let lo := q.toDyadic prec
  let exact :=
    if 0 ≤ prec then
      decide (q.den.isPowerOfTwo ∧ q.den.log2 ≤ prec.toNat)
    else
      lo.toRat = q
  let radius := if exact then 0 else Dyadic.ofIntWithPrec 1 prec
  ⟨lo, 0, radius⟩

end DyadicComplexBall

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
