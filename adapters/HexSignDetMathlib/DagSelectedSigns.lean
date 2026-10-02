/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.DagSelectedSigns
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.SignDet.Dag

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hsign in
/-- Every claimed sign accepted from an arbitrary supplied graph is the
mathematical sign at the original selected root, in the requested query order.
This uses the shared query semantics and the existing selected-sign theorem. -/
theorem selectedSigns_values {context : Ctx} (d : Descriptor E Ctx sign context)
    (qs : List (DensePoly E)) (values : Vector Int qs.length)
    (dag : Dag E Ctx) (s : SelectedSigns d qs)
    (h : dag.selectedSigns? d qs values = some s) :
    values.toList = signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign) := by
  obtain ⟨_, _, hv, _⟩ := selectedSigns_evidence h
  simpa only [hv] using s.values_at_root f hz h1 ha hs hm hnat hsign

end Hex.SignDet.Dag
