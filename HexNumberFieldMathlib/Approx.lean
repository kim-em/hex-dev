/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.AdjoinRoot

public section

/-!
# Semantics of fixed-field approximation

This module gives executable dyadic balls their ordinary closed-disc meaning
in `ℂ` and states the enclosure and requested-radius contracts for
{name}`Hex.QAdjoin.approx`.
-/

open Metric Set

namespace Hex

namespace RefinedIsolation

/-- The local refinement budget is sufficient to reach every requested
precision for an already certified simple-root atom. -/
theorem refineTo?_isSome {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    (rep.refineTo? target strategy).isSome := by
  sorry

/-- Every successful refined result reaches the requested precision. -/
theorem refineTo?_precision {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet)
    {out : {rep' : RefinedIsolation p //
      SimpleRoot.mk rep' = SimpleRoot.mk rep}}
    (h : rep.refineTo? target strategy = some out) :
    target ≤ out.1.1.square.prec := by
  sorry

end RefinedIsolation

namespace DyadicComplexBall

/-- The complex centre represented by a dyadic complex ball. -/
@[expose]
noncomputable def center (b : DyadicComplexBall) : ℂ :=
  HexRootsMathlib.GaussDyadic.toComplex (b.re, b.im)

/-- The real radius represented by a dyadic complex ball. -/
@[expose]
noncomputable def realRadius (b : DyadicComplexBall) : ℝ :=
  HexRootsMathlib.Dyadic.toReal b.radius

/-- The ordinary closed complex disc represented by an executable ball. -/
@[expose]
noncomputable def set (b : DyadicComplexBall) : Set ℂ :=
  closedBall b.center b.realRadius

/-- Minkowski addition encloses sums of enclosed values. -/
theorem add_mem {a b : DyadicComplexBall} {z w : ℂ}
    (hz : z ∈ a.set) (hw : w ∈ b.set) :
    z + w ∈ (a.add b).set := by
  sorry

/-- Executable ball multiplication encloses products of enclosed values. -/
theorem mul_mem {a b : DyadicComplexBall} {z w : ℂ}
    (hz : z ∈ a.set) (hw : w ∈ b.set) :
    z * w ∈ (a.mul b).set := by
  sorry

/-- A successful reciprocal ball encloses the reciprocal of every enclosed
value. -/
theorem inv_mem {a b : DyadicComplexBall} {z : ℂ} {prec : Int}
    (hz : z ∈ a.set) (h : a.inv? prec = some b) :
    z⁻¹ ∈ b.set := by
  sorry

end DyadicComplexBall

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Fixed-field approximation always encloses the represented complex value. -/
theorem approx_sound (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    toComplex a rep h ∈ (a.approx rep h prec).2.set := by
  sorry

/-- The guarded approximation achieves the requested dyadic radius. -/
theorem approx_radius (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    (a.approx rep h prec).2.realRadius ≤ (2 : ℝ) ^ (-prec) := by
  sorry

end QAdjoin

end Hex
