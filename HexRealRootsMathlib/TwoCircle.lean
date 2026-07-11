/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib
public import HexRealRoots.IsolateDescartes

public section

/-!
# Deferred: Descartes engine termination (the two-circle theorem)

This module states the one deferred theorem of `HexRealRootsMathlib` and names
its prerequisite. It is the **only intentional `sorry` in the library** — every
other theorem (isolation soundness, run completeness, driver completeness for
the Sturm engine, refinement, and root identity) is complete without it.

`isolateDescartes?_isSome` says the *Descartes* engine alone never falls back to
`none` on nonzero square-free input. The Sturm engine's termination
(`isolateSturm?_isSome`) and hence the top-level driver (`isolate?_isSome`) are
already proven, so nothing downstream — including hex-rcf's decision procedure —
waits on this statement. Its value is to retire the Sturm fallback from the
trusted runtime story.

## Prerequisite: the Obreshkoff two-circle theorem

For an interval `(a, b)`, the variation count of the Möbius-transformed
polynomial is at least the number of roots in the one-circle region (the open
disc with diameter `(a, b)`) and at most the number of roots in the two-circle
region (the union of the two discs through `a` and `b` whose centres lie at
`(a+b)/2 ± i·(b−a)/(2√3)`), counted with multiplicity. Consequences: a short
interval far from all roots has count `0`, and a short interval whose two-circle
region contains one simple real root has count `1`, so at `isolationDepth p` the
Descartes worklist drains and every candidate certifies.

Unlike the Sturm termination argument, the Descartes variation counts are also
disturbed by nearby *non-real* roots, which is exactly why this statement needs
the two-circle theorem rather than the real-gap separation bound.

## Status and boundaries (from the SPEC)

- The two-circle theorem has no formalisation in any proof assistant that we
  know of. The classical proof (Obreschkoff 1963; modern treatment in
  Krandick-Mehlhorn 2006 and Eigenwillig 2008) is an induction on multiplying in
  linear and conjugate-quadratic factors, with sector inequalities on
  coefficient sequences. Elementary but long, and the effort is genuinely
  uncertain.
- **Nothing else waits for it.** `isolate?_isSome`, all soundness theorems, and
  hex-rcf's decision procedure are complete without it.
- Like the Sturm slice, it should be developed against `Polynomial ℝ` (and `ℂ`
  for the regions) with no `HexRealRoots` dependence, as a Mathlib contribution
  in its own right.

## Conformance-deletion obligation

The PR that discharges this `sorry` **must delete the Descartes stand-in
assertions** in `conformance/HexRealRoots/Conformance.lean` in the same change.
Those assertions — `(isolateDescartes? p).isSome` and
`endpoints (isolateDescartes? p) = endpoints (isolate? p)` per fixture — are the
SPEC-mandated executable stand-in for this theorem (see
[hex-real-roots.md](../SPEC/Libraries/hex-real-roots.md) §"Conformance
fixtures" and the deletion note in that conformance module). Once the theorem
carries the claim, the stand-in is redundant and is retired.
-/

namespace HexRealRootsMathlib

/-- **The Descartes engine succeeds on nonzero square-free input (deferred).**
`isolateDescartes? p ≠ none` for nonzero `p` passing the executable
`SquareFreeRat` test.

Deferred pending the Obreshkoff two-circle theorem (see the module docstring):
at `isolationDepth p` the Descartes worklist drains because each short interval's
Möbius variation count is pinned to the number of roots in its two-circle
region, which is `0` far from the roots and `1` around a single simple real
root. This is the sole intentional `sorry` in `HexRealRootsMathlib`. -/
theorem isolateDescartes?_isSome (p : Hex.ZPoly) (hp0 : p ≠ 0)
    (hp : Hex.ZPoly.SquareFreeRat p) : (Hex.isolateDescartes? p).isSome := sorry

end HexRealRootsMathlib
