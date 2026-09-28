/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerModel
public import HexRealClosureMathlib.YunInvariant

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [decK : DecidableEq K]
variable {context : Context registry} (model : Model context K)

/-- Interpret a native polynomial as a dense polynomial over the ambient field.
Zero reflection suffices even when nonzero representatives are noncanonical. -/
noncomputable def mapPoly (p : DensePoly context.Value) : DensePoly K :=
  DensePoly.Interpret.map model.value model.zero_iff p

@[simp] theorem coeff_mapPoly (p : DensePoly context.Value) (i : Nat) :
    (model.mapPoly p).coeff i = model.value (p.coeff i) :=
  DensePoly.Interpret.map_coeff model.value model.zero_iff p i

@[simp] theorem natDegree_mapPoly (p : DensePoly context.Value) :
    (model.mapPoly p).natDegree = p.natDegree :=
  DensePoly.Interpret.map_degree model.value model.zero_iff p

/-- Polynomial zero has the same unique representation before interpretation. -/
theorem mapPoly_zero (p : DensePoly context.Value) : model.mapPoly p = 0 ↔ p = 0 :=
  DensePoly.Interpret.map_eq_zero model.value model.zero_iff p

/-- The actual native Yun recurrence agrees with the lawful field computation
at every tower depth. No field instance is introduced on stored expressions. -/
theorem decompose_map (p : DensePoly context.Value) :
    Yun.Decomposition.map model.value model.zero_iff (Yun.decomposeRaw p) =
      Yun.decomposeRaw (model.mapPoly p) :=
  Yun.map_decomposeRaw model.value model.zero_iff model.sub model.mul model.div
    model.inv model.nat p

/-- A successful native result retains the same unit and multiplicity labels
when mapped to the semantic field. -/
theorem decompose_result (p : DensePoly context.Value) (unit : context.Value)
    (entries : Array (DensePoly context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries) :
    Yun.decomposeRaw (model.mapPoly p) =
      .factors (model.value unit) (entries.map fun e => (model.mapPoly e.1, e.2)) := by
  rw [← model.decompose_map, hresult]
  rfl

variable [orderK : IsStrictOrderedRing K]

/-- The interpreted output of the native recurrence passes full exact replay,
including repeated factors and nonmonic definitions. -/
theorem decompose_sound (p : DensePoly context.Value) :
    Yun.check (model.mapPoly p)
      (Yun.Decomposition.map model.value model.zero_iff (Yun.decomposeRaw p)) = true := by
  rw [model.decompose_map]
  exact Yun.decompose_sound _

/-- A component of the actual native output has precisely the original root
multiplicity in the ambient field, besides positivity, monicity and simplicity. -/
theorem decompose_factor (p : DensePoly context.Value) (hdegree : 0 < p.natDegree)
    (unit : context.Value) (entries : Array (DensePoly context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries)
    (entry : DensePoly context.Value × Nat) (he : entry ∈ entries) :
    Yun.Component (model.mapPoly p) (model.mapPoly entry.1, entry.2) := by
  have hd : 0 < (model.mapPoly p).natDegree := by
    simpa only [mapPoly, DensePoly.Interpret.map_degree] using hdegree
  exact Yun.decompose_factor (model.mapPoly p) hd _ _
    (model.decompose_result p unit entries hresult) _ (Array.mem_map.mpr ⟨entry, he, rfl⟩)

/-- Every ambient root of a nonzero native input occurs in its actual returned
array with the correct multiplicity. No optional replay premise is required. -/
theorem decompose_complete (p : DensePoly context.Value) (hp : p ≠ 0)
    (unit : context.Value) (entries : Array (DensePoly context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries) (x : K)
    (hx : (HexPolyMathlib.toPolynomial (model.mapPoly p)).IsRoot x) :
    ∃ entry ∈ entries,
      entry.2 = (HexPolyMathlib.toPolynomial (model.mapPoly p)).rootMultiplicity x ∧
        (HexPolyMathlib.toPolynomial (model.mapPoly entry.1)).IsRoot x := by
  have hp' : model.mapPoly p ≠ 0 := by
    intro hz
    exact hp ((DensePoly.Interpret.map_eq_zero model.value model.zero_iff p).mp hz)
  obtain ⟨u, es, hr, e, he, hm, hx⟩ := Yun.decompose_root (model.mapPoly p) x hp' hx
  have ht := model.decompose_result p unit entries hresult
  have hs : es = entries.map (fun e => (model.mapPoly e.1, e.2)) := by
    exact (Yun.Decomposition.factors.inj (hr.symm.trans ht)).2
  rw [hs] at he
  obtain ⟨entry, he₀, heq⟩ := Array.mem_map.mp he
  cases heq
  exact ⟨entry, he₀, hm, hx⟩

/-- Every ambient root of a nonzero input occurs in the actual native result,
without a caller-supplied result or replay premise. -/
theorem decompose_root (p : DensePoly context.Value) (hp : p ≠ 0) (x : K)
    (hx : (HexPolyMathlib.toPolynomial (model.mapPoly p)).IsRoot x) :
    ∃ unit entries, Yun.decomposeRaw p = .factors unit entries ∧
      ∃ entry ∈ entries,
        entry.2 = (HexPolyMathlib.toPolynomial (model.mapPoly p)).rootMultiplicity x ∧
          (HexPolyMathlib.toPolynomial (model.mapPoly entry.1)).IsRoot x := by
  cases hr : Yun.decomposeRaw p with
  | zero =>
    have hs := model.decompose_sound p
    rw [hr, Yun.Decomposition.map] at hs
    have hz := (Yun.check_zero_iff (model.mapPoly p)).mp hs
    exact (hp ((DensePoly.Interpret.map_eq_zero model.value model.zero_iff p).mp hz)).elim
  | factors unit entries =>
    exact ⟨unit, entries, rfl, model.decompose_complete p hp unit entries hr x hx⟩

include model decK orderK in
/-- A native produced factor has constant gcd with its derivative. This
transfers the actual computed degree, without literal field laws on syntax. -/
theorem decompose_squarefree (p : DensePoly context.Value) (hdegree : 0 < p.natDegree)
    (unit : context.Value) (entries : Array (DensePoly context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries)
    (entry : DensePoly context.Value × Nat) (he : entry ∈ entries) :
    (DensePoly.gcd entry.1 (DensePoly.derivativeImpl entry.1)).natDegree = 0 := by
  have hd : 0 < (model.mapPoly p).natDegree := by
    simpa only [mapPoly, DensePoly.Interpret.map_degree] using hdegree
  have hc := Yun.decompose_factor_gcd (model.mapPoly p) hd _ _
    (model.decompose_result p unit entries hresult) _ (Array.mem_map.mpr ⟨entry, he, rfl⟩)
  have hder := DensePoly.Interpret.map_derivative model.value model.zero_iff
    model.nat model.mul entry.1
  simp only [DensePoly.derivative_eq_derivativeImpl] at hder
  change (DensePoly.gcd (DensePoly.Interpret.map model.value model.zero_iff entry.1)
    (DensePoly.derivativeImpl (DensePoly.Interpret.map model.value model.zero_iff entry.1))).natDegree = 0 at hc
  rw [← hder, ← DensePoly.Interpret.map_gcd model.value model.zero_iff model.sub model.mul model.div,
    DensePoly.Interpret.map_degree] at hc
  exact hc

include model decK orderK in
/-- Different multiplicity labels in the actual native output have constant
computed gcd, so their root sets do not overlap in the semantic field. -/
theorem decompose_coprime (p : DensePoly context.Value) (hdegree : 0 < p.natDegree)
    (unit : context.Value) (entries : Array (DensePoly context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries)
    (a b : DensePoly context.Value × Nat) (ha : a ∈ entries) (hb : b ∈ entries)
    (hne : a.2 ≠ b.2) : (DensePoly.gcd a.1 b.1).natDegree = 0 := by
  have hd : 0 < (model.mapPoly p).natDegree := by
    simpa only [mapPoly, DensePoly.Interpret.map_degree] using hdegree
  have hc := Yun.decompose_coprime (model.mapPoly p) hd _ _
    (model.decompose_result p unit entries hresult) _ _
    (Array.mem_map.mpr ⟨a, ha, rfl⟩) (Array.mem_map.mpr ⟨b, hb, rfl⟩) hne
  change (DensePoly.gcd (DensePoly.Interpret.map model.value model.zero_iff a.1)
    (DensePoly.Interpret.map model.value model.zero_iff b.1)).natDegree = 0 at hc
  rw [← DensePoly.Interpret.map_gcd model.value model.zero_iff model.sub model.mul model.div,
    DensePoly.Interpret.map_degree] at hc
  exact hc

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.decompose_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.decompose_sound
/-- info: 'Hex.RealClosure.Tower.Model.decompose_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.decompose_complete
/-- info: 'Hex.RealClosure.Tower.Model.decompose_squarefree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.decompose_squarefree
