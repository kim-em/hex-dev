/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Kantorovich
public import HexRoots.MahlerPrec

public section

/-!
The identity of a simple root, up to isolation.

A `RefinedIsolation p` is a `DyadicRootIsolation p` refined at least to
separation precision `mahlerPrec p`: at this precision the circumscribed-disc
radius `2^{−prec}·√2` is below `sep(p)/4`, so two refined isolations isolate the
same root exactly when their circumscribed discs intersect. `Intersects` is that
single exact dyadic comparison (squared centre distance against squared radius
sum), `SimpleRoot p` takes the `Quot` of it, and `RefinedIsolation.sameRoot` is
its Boolean form for equality tests on data containing roots (see
`hex-number-field`).

Why the radius bound is part of the type: without it, a coarse isolation whose
disc overlaps several fine isolations would relate distinct roots, and the
quotient would collapse them. With every disc strictly smaller than `sep(p)/4`,
two intersecting discs contain points within `sep(p)` of both roots, forcing the
roots to coincide. That argument is semantic, so this library takes the quotient
with `Quot` (which needs no equivalence proof) and provides no
`DecidableEq (SimpleRoot p)`. The Mathlib companion proves that `Intersects`
restricted to `RefinedIsolation` is an equivalence relation whose classes are
exactly the simple roots, and hence that `sameRoot` decides equality in the
quotient. Code in the Mathlib-free layer compares roots with `sameRoot`
directly.

### The threading pattern

`SimpleRoot p` values carry no usable computational content in this layer
(nothing lifts out of the `Quot` here). Numerical work happens on
`RefinedIsolation` representatives, which are plain data. A function that
repeatedly needs high-precision approximations of the same root should refine
its representative once and pass the refined value forward:

```lean
-- DON'T: each use re-refines from the stored representative
def slow (r : RefinedIsolation p) : Foo :=
  let a := (r.1.refineTo? 32).map …
  let b := (r.1.refineTo? 64).map …   -- repeats the work up to 32
  …

-- DO: refine once, thread the refined representative forward
def fast (r : RefinedIsolation p) : Option (RefinedIsolation p × Foo) := do
  let r' ← r.refineTo? 64
  …                                   -- both uses read r' directly
  return (r', …)                      -- caller stores r' going forward
```

`refineTo?` preserves the root (`sameRoot r r' = true`, proved meaningful in the
companion), so callers can substitute the refined representative wherever the
original was used. Structures that contain a representative (such as
`AlgebraicNumber` in `hex-number-field`) should store the refined value on
return, so downstream consumers inherit the precision.
-/
namespace Hex

/-- An isolation refined at least to separation precision. At this precision the
    disc radius is below `sep(p)/4`, so two refined isolations isolate the same
    root exactly when their discs intersect. -/
@[expose] def RefinedIsolation (p : ZPoly) :=
  {iso : DyadicRootIsolation p // (mahlerPrec p : Int) ≤ iso.square.prec}

/-- The circumscribed discs intersect. A single exact dyadic comparison
    (squared centre distance against squared radius sum). -/
@[expose] def Intersects {p : ZPoly} (i₁ i₂ : RefinedIsolation p) : Prop :=
  DyadicSquare.discsMeet i₁.1.square i₂.1.square = true

instance {p : ZPoly} {i₁ i₂ : RefinedIsolation p} : Decidable (Intersects i₁ i₂) :=
  inferInstanceAs (Decidable (_ = true))

/-- The identity of a simple root, independent of which isolation witnessed it.
    (`Quot` of a bare relation; the companion proves `Intersects` is an
    equivalence on `RefinedIsolation` whose classes are the simple roots.) -/
@[expose] def SimpleRoot (p : ZPoly) := Quot (Intersects (p := p))

/-- The simple root witnessed by a refined isolation. -/
@[expose] def SimpleRoot.mk {p : ZPoly} (iso : RefinedIsolation p) : SimpleRoot p :=
  Quot.mk _ iso

/-- Boolean form of `Intersects`, used for equality tests on data containing
    roots (see `hex-number-field`). -/
@[expose] def RefinedIsolation.sameRoot {p : ZPoly} (i₁ i₂ : RefinedIsolation p) : Bool :=
  DyadicSquare.discsMeet i₁.1.square i₂.1.square

/-- Wrap an isolation as a `RefinedIsolation` when it meets the separation
    precision, deciding the subtype bound. `isolate`'s output always
    qualifies (its target has a `separationDepth ≥ mahlerPrec` floor); this
    is the constructor consumers use to record that fact. -/
def DyadicRootIsolation.toRefined? {p : ZPoly} (iso : DyadicRootIsolation p) :
    Option (RefinedIsolation p) :=
  if h : (mahlerPrec p : Int) ≤ iso.square.prec then some ⟨iso, h⟩ else none

end Hex
