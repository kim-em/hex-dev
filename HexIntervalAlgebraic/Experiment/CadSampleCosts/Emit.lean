module
import HexIntervalAlgebraic.Experiment.CadSampleCosts.Support
public meta import HexIntervalAlgebraic.Experiment.CadSampleCosts.Support
open CadSampleCosts
#cad_emit Nlsat : ∀ x : ℝ, 16*x^3-8*x^2+x+16=0 → x<0 → x^3-x^2-2<0
#cad_emit CircleParabola : ∀ x : ℝ, x^4+x^2-1=0 → x>0 → x^2-x<0
#cad_emit Circles : ∀ y : ℝ, 4*y^2-3=0 → y>0 → y-1/2>0
#cad_emit Kahan : ∀ t : ℝ, t^2-2=0 → 1<t → t<2 → 5*t^2+8*t-60<0
#cad_emit Sphere : ∀ t : ℝ, t^4-10*t^2+1=0 → 3<t → t<4 →
  1-((t^3-9*t)/4)^2-((11*t-t^3)/6)^2>0
#cad_emit Tower4 : ∀ y : ℝ, y^4-2=0 → y>1 → y-y^2<0
#cad_emit Tower8 : ∀ y : ℝ, y^8-2=0 → y>1 → y-y^2<0
