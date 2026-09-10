/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.DriverCompleteness

public section

/-!
# Total complex-root isolation

This module turns the executable option-valued isolator into a total,
proof-facing operation.  Callers supply exactly the hypotheses needed by the
completeness theorem: the polynomial is nonzero and has only simple roots.
-/

namespace HexRootsMathlib

noncomputable section

/-- Isolate all complex roots of a nonzero squarefree integer polynomial.

Unlike `Hex.ZPoly.isolateComplexRoots?`, this proof-facing wrapper cannot return `none`: its
required hypotheses discharge the driver's completeness conditions. The
result is characterized by `isolateComplexRoots_eq` as the successful executable output,
with the same atom strategy and requested-precision parameters. -/
def isolateComplexRoots (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p) (hp : p ≠ 0)
    (atomPrec : Int) (strategy : Hex.AtomStrategy := .nkThenPellet) :
    Array (Hex.DyadicRootIsolation p) :=
  (isolateComplexRoots?_exists p h hp atomPrec strategy).choose

/-- The total wrapper is exactly the successful result of `Hex.ZPoly.isolateComplexRoots?`. -/
theorem isolateComplexRoots_eq (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    Hex.ZPoly.isolateComplexRoots? p h atomPrec strategy =
      some (isolateComplexRoots p h hp atomPrec strategy) :=
  (isolateComplexRoots?_exists p h hp atomPrec strategy).choose_spec

/-- The total wrapper returns one atom for each complex root, counted with
multiplicity. -/
theorem isolateComplexRoots_count (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    (isolateComplexRoots p h hp atomPrec strategy).size =
      (HexRootsMathlib.toPolyℂ p).natDegree :=
  isolateComplexRoots?_count p h atomPrec strategy (isolateComplexRoots_eq p h hp atomPrec strategy)

/-- The semantic roots selected by the returned atoms are exactly the roots of
the input polynomial. -/
theorem isolateComplexRoots_roots (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    ((isolateComplexRoots p h hp atomPrec strategy).toList.map
      HexRootsMathlib.DyadicRootIsolation.root).toFinset =
        (HexRootsMathlib.toPolyℂ p).roots.toFinset :=
  (isolateComplexRoots?_sound p h atomPrec strategy
    (isolateComplexRoots_eq p h hp atomPrec strategy)).1

/-- Every returned atom meets the requested precision. -/
theorem isolateComplexRoots_prec (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    ∀ iso ∈ (isolateComplexRoots p h hp atomPrec strategy).toList,
      atomPrec ≤ iso.square.prec :=
  (isolateComplexRoots?_sound p h atomPrec strategy
    (isolateComplexRoots_eq p h hp atomPrec strategy)).2

/-- Distinct atoms returned by the total wrapper have disjoint closed
circumscribed discs. -/
theorem isolateComplexRoots_disjoint (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet)
    {i j : Nat} (hi : i < (isolateComplexRoots p h hp atomPrec strategy).size)
    (hj : j < (isolateComplexRoots p h hp atomPrec strategy).size) (hij : i ≠ j) :
    Disjoint
      (DyadicSquare.closedDisc (isolateComplexRoots p h hp atomPrec strategy)[i].square)
      (DyadicSquare.closedDisc (isolateComplexRoots p h hp atomPrec strategy)[j].square) :=
  isolateComplexRoots?_disjoint p h atomPrec strategy
    (isolateComplexRoots_eq p h hp atomPrec strategy) hi hj hij

end

end HexRootsMathlib
