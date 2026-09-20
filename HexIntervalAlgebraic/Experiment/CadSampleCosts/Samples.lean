/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Validate
public import Mathlib.Tactic.Linarith
public meta import HexRCF.Tactic
public section

namespace CadSampleCosts

/-- Transfer the univariate query to the paper's two-variable polynomial. -/
theorem nlsatSign (a b : ℝ) (ha : 16*a^3-8*a^2+a+16=0)
    (hneg : a<0) (hcircle : a^2+b^2=1) : a^3+2*a^2+3*b^2-5<0 := by
  have h := nlsat a ha hneg
  nlinarith

/-- The parabola relation supplies the substitution used in replay. -/
theorem circleParabolaSign (a b : ℝ) (hcircle : a^2+b^2=1)
    (hparabola : b=a^2) (hpos : a>0) : b-a<0 := by
  subst b
  apply circleParabola a _ hpos
  nlinarith [hcircle]

/-- Subtracting the two circle equations determines the first coordinate. -/
theorem circlesSign (a b : ℝ) (hc : a^2+b^2=1)
    (hd : (a-1)^2+b^2=1) (hpos : b>0) : b-a>0 := by
  have ha : a=1/2 := by nlinarith
  have hb : 4*b^2-3=0 := by rw [ha] at hc; nlinarith
  have h := circles b hb hpos
  rw [ha]
  exact h

/-- A point on Kahan's ellipse with a=1/4, b=1/16, c=1/4, d=0. -/
theorem kahanSign (t : ℝ) (ht : t^2-2=0) (hl : 1<t) (hu : t<2) :
    ((1+t)/4)^2+(t/8)^2-1<0 := by
  have h := kahan t ht hl hu
  nlinarith

/-- The primitive parameter specifies both positive sphere-section coordinates. -/
theorem sphereCoordinates : ∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 →
    2*((t^3-9*t)/4)^2=1 ∧ 3*((11*t-t^3)/6)^2=1 ∧
      (t^3-9*t)/4>0 ∧ (11*t-t^3)/6>0 := by rcf

/-- The Kahan sample satisfies the specialized ellipse equation. -/
theorem kahanCoordinates : ∀ t : ℝ, t^2=2 →
    16*((1+t)/4)^2-8*((1+t)/4)+64*(t/8)^2-3=0 := by rcf

-- Non-vacuity of every parameter domain used by the sign replays.
theorem nlsatExists : ∃ t : ℝ, 16*t^3-8*t^2+t+16=0 ∧ -1<t ∧ t<0 := by rcf
theorem parabolaExists : ∃ t : ℝ, t^4+t^2-1=0 ∧ 0<t ∧ t<1 := by rcf
theorem circlesExists : ∃ t : ℝ, 4*t^2-3=0 ∧ 0<t ∧ t<1 := by rcf
theorem kahanExists : ∃ t : ℝ, t^2-2=0 ∧ 1<t ∧ t<2 := by rcf
theorem sphereExists : ∃ t : ℝ, t^4-10*t^2+1=0 ∧ 3<t ∧ t<4 := by rcf
theorem tower4Exists : ∃ t : ℝ, t^4-2=0 ∧ 1<t ∧ t<2 := by rcf
theorem tower8Exists : ∃ t : ℝ, t^8-2=0 ∧ 1<t ∧ t<2 := by rcf

#print axioms nlsatSign
#print axioms circleParabolaSign
#print axioms circlesSign
#print axioms kahanSign
#print axioms sphereCoordinates
end CadSampleCosts
