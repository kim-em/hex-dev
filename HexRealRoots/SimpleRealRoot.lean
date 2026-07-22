/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealRoots.Refine
public import HexRealRoots.Prec
-- `import all` on the source modules so `decide` reduces the sanity checks
-- below in the kernel: the non-`@[expose]` bodies (`sturmChain`, `evalDyadic`,
-- `sturmVarAt`, `sepPrec`, `twoPow`, and the dyadic comparison behind
-- `Overlaps`) are opaque across the module boundary otherwise. Same workaround
-- as Var.lean and Refine.lean.
import all Init.Data.Array.DecidableEq
import all HexRealRoots.Basic
import all HexRealRoots.Chain
import all HexRealRoots.Var
import all HexRealRoots.Prec
import all HexRealRoots.Refine

public section

/-!
The identity of a real root, up to isolation.

A `RefinedRealIsolation p` is an isolation refined to *separation precision*:
its interval has width at most `2^{−sepPrec p}`, which is below `sep(p)/4` for
squarefree `p`. Two such isolations name the same root exactly when their
half-open intervals overlap, so `SimpleRealRoot p` is the quotient of refined
isolations by `Overlaps`.

Why the width bound lives in the type. Without it a coarse isolation could
overlap several fine ones and relate distinct roots, collapsing them in the
quotient. With both widths below `sep(p)/4`, an overlap places a point within
`sep(p)/2` of both roots, which forces the roots to coincide; conversely two
isolations of the *same* root both contain it, so they overlap. That argument
is semantic, so the quotient is taken with `Quot` (which needs no equivalence
proof) and this Mathlib-free layer provides no `DecidableEq (SimpleRealRoot p)`.
The companion `HexRealRootsMathlib` proves that `Overlaps` restricted to
`RefinedRealIsolation` is an equivalence whose classes are exactly the real
roots, and hence that `sameRoot` decides equality in the quotient. Code here
compares roots with `sameRoot` directly.

The threading pattern for representatives (mirroring hex-roots): a
`SimpleRealRoot` carries no computational content in this layer — nothing lifts
out of the `Quot`. Numerical work happens on `RefinedRealIsolation`
representatives, which are plain data. A function that repeatedly needs a
high-precision approximation of the same root should refine its representative
*once* and thread the refined value forward, rather than re-refining from a
stored coarse representative on each use. Refinement preserves the root
(`refine1_isolates_same` in the companion, so `sameRoot` is stable under it), so
callers can substitute the refined representative wherever the original was
used, and structures that store a representative should keep the refined value
on return so downstream consumers inherit the precision.
-/
namespace Hex

variable {p : ZPoly}

/-- An isolation refined to separation precision: its interval has width at
most `2^{−sepPrec p}`. At width below `sep(p)/4`, two refined isolations
isolate the same root exactly when their intervals overlap. -/
@[expose] def RefinedRealIsolation (p : ZPoly) :=
  {iso : RealRootIsolation p //
    iso.interval.upper - iso.interval.lower ≤ twoPow (-(sepPrec p : Int))}

/-- The half-open intervals of two refined isolations intersect:
`max lower₁ lower₂ < min upper₁ upper₂`. Core `Dyadic` has no `Min`/`Max`
instance, so the max and min are written with explicit `if`s; the whole test
is a single dyadic comparison at runtime. -/
@[expose] def Overlaps (i₁ i₂ : RefinedRealIsolation p) : Prop :=
  (if i₁.1.interval.lower ≤ i₂.1.interval.lower then i₂.1.interval.lower
    else i₁.1.interval.lower) <
  (if i₁.1.interval.upper ≤ i₂.1.interval.upper then i₁.1.interval.upper
    else i₂.1.interval.upper)

instance (i₁ i₂ : RefinedRealIsolation p) : Decidable (Overlaps i₁ i₂) :=
  inferInstanceAs (Decidable (_ < _))

/-- The identity of a real root, independent of which isolation witnessed it:
the quotient of refined isolations by interval overlap. -/
def SimpleRealRoot (p : ZPoly) := Quot (Overlaps (p := p))

/-- Package a refined isolation as a root identity. -/
def SimpleRealRoot.mk (iso : RefinedRealIsolation p) : SimpleRealRoot p :=
  Quot.mk _ iso

/-- Boolean form of `Overlaps`, used for equality tests on data containing
roots. The companion proves it decides equality in `SimpleRealRoot p`. -/
@[expose] def RefinedRealIsolation.sameRoot (i₁ i₂ : RefinedRealIsolation p) : Bool :=
  decide (Overlaps i₁ i₂)

/-- Refine an isolation to separation precision and package it as a
`RefinedRealIsolation`. Refinement runs `refineTo (sepPrec p)`; the width test
that follows is `some` on any honest isolation of a squarefree `p` (the
companion's `refine1_isolates_same` shows `refineTo` actually shrinks below
`2^{−sepPrec p}`, so the `none` branch is unreachable there). It is `Option`
only because on junk data violating the isolation semantics `refineTo` can
return its input unshrunk. This is the obvious producer the threading pattern
needs: call it once, then thread the refined value forward. -/
@[expose] def RealRootIsolation.refined (iso : RealRootIsolation p) :
    Option (RefinedRealIsolation p) :=
  let r := iso.refineTo (sepPrec p)
  if h : r.interval.upper - r.interval.lower ≤ twoPow (-(sepPrec p : Int)) then
    some ⟨r, h⟩
  else none

/-! Sanity checks (kept light; conformance lives in the shared sub-project).

Kernel reduction of `Overlaps`/`sameRoot` only needs a dyadic comparison, but
the `RefinedRealIsolation` width proof reduces `sepPrec p`, which routes through
`ceilSqrt` for degree `≥ 2` and so does not reduce in the kernel. The checks
below therefore use degree-1 polynomials, where `sepPrec p = 0` and the width
bound is `twoPow 0 = 1`. Cross-root (`sameRoot = false`) behaviour needs two
roots, hence degree `≥ 2`, so it is exercised by `#eval` in the conformance
suite instead (a degree-1 polynomial has a single root, so every honest pair of
its isolations overlaps). -/

-- `p = x − 5`, root at `5`. Two honest isolations at separation precision:
-- `(4, 5]` (width `1 = twoPow 0`) and `(9/2, 5]` (width `1/2`). Chain
-- `[x − 5, 1]`; at `4` evals `(−1, 1)` → 1 variation, at `9/2` `(−1/2, 1)` → 1,
-- at `5` `(0, 1)` → 0, so both intervals have Sturm count `1`.
private def r1 : RefinedRealIsolation (DensePoly.ofCoeffs #[(-5 : Int), 1]) :=
  ⟨⟨⟨Dyadic.ofInt 4, Dyadic.ofInt 5, by decide⟩, by decide⟩, by decide⟩
private def r2 : RefinedRealIsolation (DensePoly.ofCoeffs #[(-5 : Int), 1]) :=
  ⟨⟨⟨(Dyadic.ofInt 9) >>> (1 : Int), Dyadic.ofInt 5, by decide⟩, by decide⟩, by decide⟩

-- Both isolate the single root `5`, so their intervals overlap: `max 4 (9/2) =
-- 9/2 < 5 = min 5 5`. `sameRoot` is reflexive and identifies the two.
example : Overlaps r1 r2 := by decide
example : r1.sameRoot r2 = true := by decide
example : r1.sameRoot r1 = true := by decide
example : r2.sameRoot r2 = true := by decide

end Hex
