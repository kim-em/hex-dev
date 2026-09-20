/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Support
public meta import HexIntervalAlgebraic.Experiment.CadSampleCosts.Support
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Nlsat.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.CircleParabola.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Circles.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Kahan.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Sphere.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Tower4.Replay
public import HexIntervalAlgebraic.Experiment.CadSampleCosts.Tower8.Replay

public section
namespace CadSampleCosts

theorem nlsat : ∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0 :=
  (cad_correspondence% (∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0)).mp Nlsat.result

theorem circleParabola : ∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0 :=
  (cad_correspondence% (∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0)).mp CircleParabola.result

theorem circles : ∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0 :=
  (cad_correspondence% (∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0)).mp Circles.result

theorem kahan : ∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0 :=
  (cad_correspondence% (∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0)).mp Kahan.result

theorem sphere : ∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0 :=
  (cad_correspondence% (∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 → 1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0)).mp Sphere.result

theorem tower4 : ∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0 :=
  (cad_correspondence% (∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0)).mp Tower4.result

theorem tower8 : ∀ y : ℝ, y^8-2=0 → y>1 → y-y^2<0 :=
  (cad_correspondence% (∀ y : ℝ, y^8-2=0 → y>1 → y-y^2<0)).mp Tower8.result

end CadSampleCosts
