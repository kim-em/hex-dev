/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRefinement
public import HexRealClosureMathlib.TowerModel
public import HexSignDetMathlib.RootProducer

public section

namespace Hex.RealClosure.Tower.Model

open HexRealRootsMathlib Hex.SignDet

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [decK : DecidableEq K] [orderK : IsStrictOrderedRing K] [closedK : IsRealClosed K]
variable {parent : Context registry} (model : Model parent K)
variable {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
variable {head : DensePoly parent.Value} {a b : Endpoint parent.Value}
variable (encoding : SignDet.Reencoding source head a b)

/-- Interpret the actual checked refinement, with its own new immutable context. -/
noncomputable def refine : Model (parent.refine encoding).extension.context K :=
  (congrArg Extension.context (parent.refine encoding).canonical).symm ▸ model.adjoin encoding.target

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem transport_value {context other : Context registry} (h : context = other)
    (m : Model context K) (x : context.Value) (y : other.Value) (hy : HEq y x) :
    (h ▸ m).value y = m.value x := by
  cases h
  cases eq_of_heq hy
  rfl

/-- Checked persistent refinement preserves the selected value of every old
stored expression, including canonical zero and noncanonical nonzero values. -/
theorem refine_value (value : (parent.adjoin source).context.Value) :
    (model.refine encoding).value ((parent.refine encoding).transport value) =
      (model.adjoin source).value value := by
  unfold refine
  rw [transport_value _ _ _ _ (parent.refine_transport encoding value),
    model.adjoin_ofPoly, model.adjoin_value source value,
    model.adjoin_generator, model.adjoin_generator,
    encoding.root_eq_source model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign]

include model decK orderK closedK in
/-- Canonical zero is preserved and reflected by the actual native conversion. -/
theorem refine_zero (value : (parent.adjoin source).context.Value) :
    (parent.refine encoding).transport value = 0 ↔ value = 0 := by
  rw [← (model.refine encoding).zero_iff, model.refine_value encoding,
    (model.adjoin source).zero_iff]

include model decK orderK closedK in
/-- Refinement preserves actual semantic equality results. -/
theorem refine_equal (x y : (parent.adjoin source).context.Value) :
    (parent.refine encoding).extension.context.equal
      ((parent.refine encoding).transport x) ((parent.refine encoding).transport y) =
      (parent.adjoin source).context.equal x y := by
  rw [(model.refine encoding).equal_spec, (model.adjoin source).equal_spec,
    model.refine_value encoding, model.refine_value encoding]

include model decK orderK closedK in
/-- Refinement preserves actual ordered comparison results. -/
theorem refine_compare (x y : (parent.adjoin source).context.Value) :
    (parent.refine encoding).extension.context.compare
      ((parent.refine encoding).transport x) ((parent.refine encoding).transport y) =
      (parent.adjoin source).context.compare x y := by
  rw [(model.refine encoding).compare_spec, (model.adjoin source).compare_spec,
    model.refine_value encoding, model.refine_value encoding]

/-- Every new-context value has its actual representative at the same selected
root. This also characterizes values not obtained by transport. -/
theorem refine_polynomial (value : (parent.refine encoding).extension.context.Value) :
    (model.refine encoding).value value =
      (HexPolyMathlib.Interpret.interpret model.value model.zero_iff
        ((parent.refine encoding).polynomial value)).eval
          ((model.adjoin source).value (parent.adjoin source).generator) := by
  unfold refine
  rw [transport_value _ _ _ _ (cast_heq _ _).symm,
    model.adjoin_value encoding.target, model.adjoin_generator,
    model.adjoin_generator,
    encoding.root_eq_source model.value model.zero_iff model.one model.add model.sub
      model.mul model.nat model.sign]
  rfl

/-- A persistent checked definition change preserves the whole mathematical
value field, not only the generator or transported values. -/
theorem refine_field : (model.refine encoding).field = (model.adjoin source).field := by
  apply le_antisymm
  · rintro x ⟨value, rfl⟩
    refine ⟨parent.ofPoly source ((parent.refine encoding).polynomial value), ?_⟩
    rw [model.adjoin_ofPoly, model.refine_polynomial]
  · rintro x ⟨value, rfl⟩
    exact ⟨(parent.refine encoding).transport value, model.refine_value encoding value⟩

/-- The actual normalized native polynomial conversion is the shared
zero-reflecting coefficient map. No literal field laws are used. -/
theorem refine_map (p : DensePoly (parent.adjoin source).context.Value) :
    (parent.refine encoding).mapPoly p =
      DensePoly.Interpret.map (parent.refine encoding).transport
        (model.refine_zero encoding) p := by
  have h := DensePoly.Interpret.map_ofCoeffs (parent.refine encoding).transport
    (model.refine_zero encoding) p.toArray
  rw [DensePoly.ofCoeffs_toArray] at h
  exact h.symm

include model decK orderK closedK in
/-- Polynomial transport preserves the degree actually stored by the source. -/
theorem refine_degree (p : DensePoly (parent.adjoin source).context.Value) :
    ((parent.refine encoding).mapPoly p).natDegree = p.natDegree := by
  rw [model.refine_map]
  exact DensePoly.Interpret.map_degree _ _ p

/-- Every converted polynomial has exactly the same ambient interpretation. -/
theorem refine_poly (p : DensePoly (parent.adjoin source).context.Value) :
    HexPolyMathlib.Interpret.interpret (model.refine encoding).value
      (model.refine encoding).zero_iff ((parent.refine encoding).mapPoly p) =
      HexPolyMathlib.Interpret.interpret (model.adjoin source).value
        (model.adjoin source).zero_iff p := by
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret,
    HexPolyMathlib.Interpret.coeff_interpret, model.refine_map,
    DensePoly.Interpret.map_coeff, model.refine_value]

private theorem refine_endpoint (endpoint : Endpoint (parent.adjoin source).context.Value) :
    (endpoint.map (parent.refine encoding).transport).map (model.refine encoding).value =
      endpoint.map (model.adjoin source).value := by
  cases endpoint <;> simp only [Endpoint.map, model.refine_value]

private theorem refine_domain (p : DensePoly (parent.adjoin source).context.Value)
    (lower upper : Endpoint (parent.adjoin source).context.Value) :
    HexSturmMathlib.Domain (model.refine encoding).value (model.refine encoding).zero_iff
      ((parent.refine encoding).mapPoly p)
      (lower.map (parent.refine encoding).transport)
      (upper.map (parent.refine encoding).transport) ↔
    HexSturmMathlib.Domain (model.adjoin source).value (model.adjoin source).zero_iff p lower upper := by
  unfold HexSturmMathlib.Domain
  rw [model.refine_poly]
  cases lower <;> cases upper <;>
    simp only [Endpoint.map, HexSturmMathlib.EndpointLt, HexSturmMathlib.Nonvanishing,
      model.refine_value]

variable (descriptor : SignDet.Descriptor (parent.adjoin source).context.Value Signature
  (parent.adjoin source).context.sign (parent.adjoin source).context.signature)

include model decK orderK closedK in
private theorem refine_wellFormed :
    ((parent.refine encoding).mapRaw descriptor).wellFormed = true := by
  have hw := (SignDet.RawDescriptor.check_eq descriptor.accepted).1
  unfold Refinement.mapRaw SignDet.RawDescriptor.wellFormed
  rw [model.refine_degree]
  exact hw

include model decK orderK closedK in
/-- Rebuilding a later descriptor always succeeds after a checked refinement.
Its new evidence is generated against the new immutable predecessor. -/
theorem refine_descriptor :
    ∃ converted, (parent.refine encoding).mapDescriptor? descriptor = some converted := by
  let old := model.adjoin source
  let next := model.refine encoding
  obtain ⟨hw, hctx, hc, hcount⟩ := SignDet.RawDescriptor.check_eq descriptor.accepted
  have hdom := descriptor.evidence.check_domain old.value old.zero_iff old.one
    old.add old.sub old.mul old.nat _ old.sign _ _ _ _ _ hc
  have hone := descriptor.evidence.count_roots old.value old.zero_iff old.one
    old.add old.sub old.mul old.nat _ old.sign _ _ _ _ _ hc descriptor.raw.signs
  have hlookup := descriptor.evidence.table_lookup hc descriptor.raw.signs
  have hcard := hone.symm.trans (hlookup.symm.trans hcount)
  change ∃ converted, SignDet.Descriptor.validate _ _ _ = some converted
  apply (SignDet.Descriptor.validate_success_formal next.value next.zero_iff next.one
    next.add next.sub next.mul next.nat next.neg next.inv _ next.sign _ _).mpr
  refine ⟨rfl, model.refine_wellFormed encoding descriptor,
    (model.refine_domain encoding _ _ _).mpr hdom, ?_⟩
  dsimp only [next, old] at hcard ⊢
  simp only [Refinement.mapRaw, model.refine_poly, model.refine_endpoint]
  convert hcard using 2
  apply Finset.filter_congr
  intro x hx
  simp only [signsAt]
  rw [descriptor.raw.querySigns (model.adjoin source).value (model.adjoin source).zero_iff
    (model.adjoin source).nat (model.adjoin source).mul hw x]


/-- The later descriptor returned by actual revalidation selects exactly the
same ambient root; its predecessor coefficients now have fresh bindings. -/
theorem refine_root
    (converted : SignDet.Descriptor (parent.refine encoding).extension.context.Value Signature
      (parent.refine encoding).extension.context.sign (parent.refine encoding).extension.context.signature)
    (hconverted : (parent.refine encoding).mapDescriptor? descriptor = some converted) :
    converted.root (model.refine encoding).value (model.refine encoding).zero_iff
      (model.refine encoding).one (model.refine encoding).add (model.refine encoding).sub
      (model.refine encoding).mul (model.refine encoding).nat (model.refine encoding).sign =
    descriptor.root (model.adjoin source).value (model.adjoin source).zero_iff
      (model.adjoin source).one (model.adjoin source).add (model.adjoin source).sub
      (model.adjoin source).mul (model.adjoin source).nat (model.adjoin source).sign := by
  let old := model.adjoin source
  let next := model.refine encoding
  have hraw := SignDet.Descriptor.build_raw
    (SignDet.Descriptor.validate_eq_some.mp hconverted)
  obtain ⟨hx, hs⟩ := converted.root_spec next.value next.zero_iff next.one next.add
    next.sub next.mul next.nat next.sign
  apply descriptor.root_unique old.value old.zero_iff old.one old.add old.sub old.mul old.nat old.sign
  · rw [hraw] at hx
    dsimp only [Refinement.mapRaw, next] at hx
    simpa only [model.refine_poly, model.refine_endpoint] using hx
  · rw [descriptor.derivatives_at old.value old.zero_iff old.mul old.nat]
    rw [converted.derivatives_at next.value next.zero_iff next.mul next.nat] at hs
    rw [hraw] at hs
    dsimp only [Refinement.mapRaw, next] at hs
    simpa only [model.refine_poly] using hs


/-- Every value at the revalidated later root preserves its interpretation,
using the actual native polynomial conversion and packing operations. -/
theorem refine_later
    (converted : SignDet.Descriptor (parent.refine encoding).extension.context.Value Signature
      (parent.refine encoding).extension.context.sign (parent.refine encoding).extension.context.signature)
    (hconverted : (parent.refine encoding).mapDescriptor? descriptor = some converted)
    (value : ((parent.adjoin source).context.adjoin descriptor).context.Value) :
    ((model.refine encoding).adjoin converted).value
      ((parent.refine encoding).mapValue descriptor converted value) =
    ((model.adjoin source).adjoin descriptor).value value := by
  unfold Refinement.mapValue
  rw [Model.adjoin_ofPoly, model.refine_poly,
    Model.adjoin_generator, model.refine_root encoding descriptor converted hconverted,
    (model.adjoin source).adjoin_value descriptor value,
    (model.adjoin source).adjoin_generator]


end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.refine_value' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_value

/-- info: 'Hex.RealClosure.Tower.Model.refine_field' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_field

/-- info: 'Hex.RealClosure.Tower.Model.refine_degree' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_degree

/-- info: 'Hex.RealClosure.Tower.Model.refine_descriptor' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_descriptor

/-- info: 'Hex.RealClosure.Tower.Model.refine_root' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_root

/-- info: 'Hex.RealClosure.Tower.Model.refine_later' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.refine_later
