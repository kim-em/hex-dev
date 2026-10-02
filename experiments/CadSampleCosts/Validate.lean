/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import CadSampleCosts.Support
public meta import CadSampleCosts.Support
public import CadSampleCosts.Vanishing.Replay
public import CadSampleCosts.Vanishing.Kernel
public import CadSampleCosts.Nlsat.Replay
public import CadSampleCosts.Nlsat.Kernel
public import CadSampleCosts.CircleParabola.Replay
public import CadSampleCosts.CircleParabola.Kernel
public import CadSampleCosts.Circles.Replay
public import CadSampleCosts.Circles.Kernel
public import CadSampleCosts.Kahan.Replay
public import CadSampleCosts.Kahan.Kernel
public import CadSampleCosts.Sphere.Replay
public import CadSampleCosts.Sphere.Kernel
public import CadSampleCosts.Tower4.Replay
public import CadSampleCosts.Tower4.Kernel
public import CadSampleCosts.Tower8.Replay
public import CadSampleCosts.Tower8.Kernel

public section
namespace CadSampleCosts

theorem vanishing : ∀ x : ℝ, x^4+x^2-1=0 → (x^2)^2+x^2-1=0 :=
  (cad_correspondence% (∀ x : ℝ, x^4+x^2-1=0 → (x^2)^2+x^2-1=0)).mp Vanishing.result

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

#print axioms CadSampleCosts.nlsatSign

#print axioms CadSampleCosts.circleParabolaSign

#print axioms CadSampleCosts.circlesSign

#print axioms CadSampleCosts.kahanSign

#print axioms CadSampleCosts.sphereCoordinates

#print axioms CadSampleCosts.kahanCoordinates

#print axioms CadSampleCosts.nlsatExists

#print axioms CadSampleCosts.parabolaExists

#print axioms CadSampleCosts.circlesExists

#print axioms CadSampleCosts.kahanExists

#print axioms CadSampleCosts.sphereExists

#print axioms CadSampleCosts.tower4Exists

#print axioms CadSampleCosts.tower8Exists

#print axioms CadSampleCosts.nlsatSampleExists

#print axioms CadSampleCosts.parabolaSampleExists

#print axioms CadSampleCosts.circlesSampleExists

#print axioms CadSampleCosts.sphereSample

#print axioms CadSampleCosts.Vanishing.Kernel.accepted

#print axioms CadSampleCosts.Vanishing.accepted

#print axioms CadSampleCosts.Vanishing.result

#print axioms CadSampleCosts.Vanishing.sign

#print axioms CadSampleCosts.Nlsat.Kernel.accepted

#print axioms CadSampleCosts.Nlsat.accepted

#print axioms CadSampleCosts.Nlsat.result

#print axioms CadSampleCosts.Nlsat.sign

#print axioms CadSampleCosts.Nlsat.sample

#print axioms CadSampleCosts.CircleParabola.Kernel.accepted

#print axioms CadSampleCosts.CircleParabola.accepted

#print axioms CadSampleCosts.CircleParabola.result

#print axioms CadSampleCosts.CircleParabola.sign

#print axioms CadSampleCosts.CircleParabola.sample

#print axioms CadSampleCosts.Circles.Kernel.accepted

#print axioms CadSampleCosts.Circles.accepted

#print axioms CadSampleCosts.Circles.result

#print axioms CadSampleCosts.Circles.sign

#print axioms CadSampleCosts.Circles.sample

#print axioms CadSampleCosts.Kahan.Kernel.accepted

#print axioms CadSampleCosts.Kahan.accepted

#print axioms CadSampleCosts.Kahan.result

#print axioms CadSampleCosts.Kahan.sign

#print axioms CadSampleCosts.Kahan.sample

#print axioms CadSampleCosts.Sphere.Kernel.accepted

#print axioms CadSampleCosts.Sphere.accepted

#print axioms CadSampleCosts.Sphere.result

#print axioms CadSampleCosts.Sphere.sign

#print axioms CadSampleCosts.Sphere.sample

#print axioms CadSampleCosts.Tower4.Kernel.accepted

#print axioms CadSampleCosts.Tower4.accepted

#print axioms CadSampleCosts.Tower4.result

#print axioms CadSampleCosts.Tower4.sign

#print axioms CadSampleCosts.Tower8.Kernel.accepted

#print axioms CadSampleCosts.Tower8.accepted

#print axioms CadSampleCosts.Tower8.result

#print axioms CadSampleCosts.Tower8.sign

end CadSampleCosts
