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

Unlike `Hex.isolate`, this proof-facing wrapper cannot return `none`: its
required hypotheses discharge the driver's completeness conditions. The
result is characterized by `isolate!_eq` as the successful executable output,
with the same atom strategy and requested-precision parameters. -/
def isolate! (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p) (hp : p ≠ 0)
    (atomPrec : Int) (strategy : Hex.AtomStrategy := .nkThenPellet) :
    Array (Hex.DyadicRootIsolation p) :=
  (isolate_exists p h hp atomPrec strategy).choose

/-- The total wrapper is exactly the successful result of `Hex.isolate`. -/
theorem isolate!_eq (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    Hex.isolate p h atomPrec strategy = some (isolate! p h hp atomPrec strategy) :=
  (isolate_exists p h hp atomPrec strategy).choose_spec

/-- The total wrapper returns one atom for each complex root, counted with
multiplicity. -/
theorem isolate!_count (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    (isolate! p h hp atomPrec strategy).size =
      (HexRootsMathlib.toPolyℂ p).natDegree :=
  isolate_count p h atomPrec strategy (isolate!_eq p h hp atomPrec strategy)

/-- The semantic roots selected by the returned atoms are exactly the roots of
the input polynomial. -/
theorem isolate!_roots (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    ((isolate! p h hp atomPrec strategy).toList.map
      HexRootsMathlib.DyadicRootIsolation.root).toFinset =
        (HexRootsMathlib.toPolyℂ p).roots.toFinset :=
  (isolate_sound p h atomPrec strategy
    (isolate!_eq p h hp atomPrec strategy)).1

/-- Every returned atom meets the requested precision. -/
theorem isolate!_prec (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet) :
    ∀ iso ∈ (isolate! p h hp atomPrec strategy).toList,
      atomPrec ≤ iso.square.prec :=
  (isolate_sound p h atomPrec strategy
    (isolate!_eq p h hp atomPrec strategy)).2

/-- Distinct atoms returned by the total wrapper have disjoint closed
circumscribed discs. -/
theorem isolate!_disjoint (p : Hex.ZPoly) (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) (atomPrec : Int)
    (strategy : Hex.AtomStrategy := .nkThenPellet)
    {i j : Nat} (hi : i < (isolate! p h hp atomPrec strategy).size)
    (hj : j < (isolate! p h hp atomPrec strategy).size) (hij : i ≠ j) :
    Disjoint
      (DyadicSquare.closedDisc (isolate! p h hp atomPrec strategy)[i].square)
      (DyadicSquare.closedDisc (isolate! p h hp atomPrec strategy)[j].square) :=
  isolate_disjoint p h atomPrec strategy
    (isolate!_eq p h hp atomPrec strategy) hi hj hij

end

end HexRootsMathlib
