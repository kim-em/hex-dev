/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.QueryHandle
public import HexSignDetMathlib.SelectedProducer

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hsign hn hi in
/-- Every validated descriptor with lawful coefficients admits its actual
prepared handle. This uses the named #10389 bridge and assumes no successful
query or preparation as a premise. -/
theorem Descriptor.prepareQueries_success {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    ∃ h : QueryHandle d, d.prepareQueries = some h := by
  obtain ⟨s, hb⟩ := d.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi []
  exact d.prepareQueries_ofBuild s hb

include hz h1 ha hs hm hnat hsign hn hi in
/-- The prepared selected-sign operation succeeds for every query list,
using the actual ordinary producer and the named #10389 bridge. -/
theorem QueryHandle.buildSigns_success {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (qs : List (DensePoly E)) :
    ∃ s : SelectedSigns d qs, h.buildSigns qs = .ok s := by
  rw [h.buildSigns_eq]
  exact d.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi qs

include hz h1 ha hs hm hnat hsign hn hi in
/-- The cached domain preserves the original root and ordered query signs.
This includes empty lists, repetitions and zero answers, using only the
shared proved root-sum theorem. -/
theorem QueryHandle.buildSigns_roots {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (qs : List (DensePoly E)) :
    ∃ s : SelectedSigns d qs, h.buildSigns qs = .ok s ∧
      s.values.toList = signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign) := by
  rw [h.buildSigns_eq]
  exact d.buildSigns_roots f hz h1 ha hs hm hnat hsign hn hi qs

include hz h1 ha hs hm hnat hsign hn hi in
/-- Cached singleton queries never take their diagnostic zero fallback
under lawful coefficients. -/
theorem QueryHandle.signAt_success {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (q : DensePoly E) :
    ∃ s : SelectedSigns d [q], h.buildSigns [q] = .ok s ∧ h.signAt q = s.value := by
  obtain ⟨s, hs, hv⟩ := d.signAt_success f hz h1 ha hs hm hnat hsign hn hi q
  exact ⟨s, (h.buildSigns_eq [q]).trans hs, (h.signAt_eq q).trans hv⟩

include hz h1 ha hs hm hnat hsign hn hi in
/-- The cached total singleton sign is evaluation at the original selected
root, with the same named #10389 dependency as the ordinary operation. -/
theorem QueryHandle.signAt_correct {context : Ctx}
    {d : Descriptor E Ctx sign context} (h : QueryHandle d) (q : DensePoly E) :
    h.signAt q = (SignType.sign ((interpret f hz q).eval
      (d.root f hz h1 ha hs hm hnat hsign)) : Int) := by
  rw [h.signAt_eq]
  exact d.signAt_correct f hz h1 ha hs hm hnat hsign hn hi q

end Hex.SignDet
