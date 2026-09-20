/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import CadSampleCosts.Support
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Real.Sqrt
public meta import HexRCF.Tactic
public section

namespace CadSampleCosts

/-- Transfer the univariate query to the paper's two-variable polynomial. -/
theorem nlsatSign (query : ∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0) (a b : ℝ) (ha : 16*a^3-8*a^2+a+16=0)
    (hneg : a<0) (hcircle : a^2+b^2=1) : a^3+2*a^2+3*b^2-5<0 := by
  have h := query a ha hneg
  nlinarith

/-- The parabola relation supplies the substitution used in replay. -/
theorem circleParabolaSign (query : ∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0) (a b : ℝ) (hcircle : a^2+b^2=1)
    (hparabola : b=a^2) (hpos : a>0) : b-a<0 := by
  subst b
  apply query a _ hpos
  nlinarith [hcircle]

/-- Subtracting the two circle equations determines the first coordinate. -/
theorem circlesSign (query : ∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0) (a b : ℝ) (hc : a^2+b^2=1)
    (hd : (a-1)^2+b^2=1) (hpos : b>0) : b-a>0 := by
  have ha : a=1/2 := by nlinarith
  have hb : 4*b^2-3=0 := by rw [ha] at hc; nlinarith
  have h := query b hb hpos
  rw [ha]
  exact h

/-- A point on Kahan's ellipse with a=1/4, b=1/16, c=1/4, d=0. -/
theorem kahanSign (query : ∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0) (t : ℝ) (ht : t^2-2=0) (hl : 1<t) (hu : t<2) :
    ((1+t)/4)^2+(t/8)^2-1<0 := by
  have h := query t ht hl hu
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

/-- Both chosen NLSAT coordinates exist, with the negative lifted root. -/
theorem nlsatSampleExists : ∃ a b : ℝ, 16*a^3-8*a^2+a+16=0 ∧
    -1<a ∧ a<0 ∧ b<0 ∧ a^2+b^2=1 := by
  obtain ⟨a, ha, hl, hu⟩ := nlsatExists
  have hsq : 0 < 1-a^2 := by nlinarith
  refine ⟨a, -Real.sqrt (1-a^2), ha, hl, hu, ?_, ?_⟩
  · have := Real.sqrt_pos.2 hsq
    linarith
  · have := Real.sq_sqrt hsq.le
    nlinarith

/-- The positive lifted circle root can be chosen to equal the parabola value. -/
theorem parabolaSampleExists : ∃ a b : ℝ, a^2+b^2=1 ∧ b=a^2 ∧ a>0 ∧ b>0 := by
  obtain ⟨a, ha, hl, _⟩ := parabolaExists
  refine ⟨a, a^2, ?_, rfl, hl, sq_pos_of_pos hl⟩
  nlinarith [ha]

/-- Both circle equations hold at the selected upper intersection. -/
theorem circlesSampleExists : ∃ a b : ℝ, a^2+b^2=1 ∧ (a-1)^2+b^2=1 ∧ b>0 := by
  obtain ⟨b, hb, hl, _⟩ := circlesExists
  exact ⟨1/2, b, by nlinarith, by nlinarith, hl⟩

/-- Join the sphere-section coordinate identities to its sign query. -/
theorem sphereSample (query : ∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 →
    1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0) (t : ℝ)
    (ht : t^4-10*t^2+1=0) (hl : 3<t) (hu : t<4) :
    2*((t^3-9*t)/4)^2=1 ∧ 3*((11*t-t^3)/6)^2=1 ∧
    (t^3-9*t)/4>0 ∧ (11*t-t^3)/6>0 ∧
    1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0 := by
  obtain ⟨ha, hb, hap, hbp⟩ := sphereCoordinates t ht hl hu
  exact ⟨ha, hb, hap, hbp, query t ht hl hu⟩

end CadSampleCosts
