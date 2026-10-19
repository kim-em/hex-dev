/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Algebraic
public import HexRealRootsTheory.RealClosed
public import HexSignDet.Conformance
public meta import HexRealClosure.Algebraic
public meta import HexSignDet.Conformance

public section

/-! Restore literal algebraic coefficients from supplied lower-level evidence.
The child certificate is checked in the ordinary kernel; no producer runs in
these examples. Cross-level graph serialization is a separate interface. -/
namespace Hex.RealClosure.Algebraic.CoefficientSignsConformance

open Hex.SignDet Hex.SignDet.Conformance
open scoped Hex

/-- A count-one source descriptor from the existing literal kernel replay. -/
@[expose] def source : Descriptor Rat Nat Sturm.orderSign 7 := by
  have h := RawDescriptor.check_eq selected_kernel.1
  have hc : (Replay.leaf singletonNode).check Sturm.orderSign 7 singletonRaw.head
      singletonRaw.lower singletonRaw.upper singletonRaw.queries = true := by
    obtain ⟨hc, _⟩ := h.2.2
    exact hc
  exact Descriptor.ofTable singletonRaw (.leaf singletonNode) h.1 h.2.1 hc (by
    obtain ⟨_, hone⟩ := h.2.2
    exact hone)

theorem source_raw : source.raw = singletonRaw := by
  simp only [source, Descriptor.ofTable_raw]

@[expose] def context := Context.adjoin source (fun _ => true)
@[expose] def stored : DensePoly Rat := Sturm.Fixtures.p + 2 * Sturm.Fixtures.x

private theorem query_eq : context.queryPoly stored = 2 * Sturm.Fixtures.x := by
  simp only [Context.queryPoly, Context.queryRemainder, context,
    Context.root_adjoin, source_raw, stored, singletonRaw, DensePoly.pseudoDivMod,
    ← Array.foldl_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
private theorem child_checked :
    source.checkSigns [2 * Sturm.Fixtures.x] #v[1] (.leaf firstNode) = true := by
  simp only [Descriptor.checkSigns, source_raw, RawDescriptor.checkSigns,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

set_option maxRecDepth 32768 in
/-- Evidence for a wrong sign, a different query or a mismatched context key rejects.
`Context.signPoly_checked` fixes its actual reduced query. -/
theorem rejected_kernel :
    source.checkSigns [2 * Sturm.Fixtures.x] #v[-1] (.leaf firstNode) = false ∧
    source.checkSigns [stored] #v[1] (.leaf firstNode) = false ∧
    source.checkSigns [2 * Sturm.Fixtures.x] #v[1]
      (.leaf {firstNode with context := 8}) = false := by
  simp only [Descriptor.checkSigns, source_raw, RawDescriptor.checkSigns,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmTheory.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- The child replay proves the exact cached sign used by the actual native
operation, including its preliminary query reduction. -/
theorem sign_checked : context.signPoly stored = 1 := by
  let signs : SelectedSigns context.root [context.queryPoly stored] :=
    ⟨#v[1], .leaf firstNode, by
      rw [query_eq]
      simpa only [context, Context.root_adjoin] using child_checked⟩
  have h := context.signPoly_checked (fun q : Rat => (q : ℝ))
    (fun _ => Rat.cast_eq_zero) (by simp)
    (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    (fun _ => Rat.cast_neg _) (fun _ => Rat.cast_inv _) stored signs
  simpa [signs, SelectedSigns.value] using h

/-- The stored representative has degree two, whereas its selected-root query
has degree one. Restoration retains that distinction literally. -/
theorem restore_literal :
    (Element.restore stored 1 sign_checked (by decide +kernel)).polynomial = stored ∧
    (Element.restore stored 1 sign_checked (by decide +kernel)).sign = 1 :=
  ⟨Element.restore_polynomial _ _ _ _, Element.restore_sign _ _ _ _⟩

/-- The proof-directed and independently checked constructors return exactly
the same coefficient, not only semantically equal values. -/
theorem restore_checked :
    Element.restore? (context := context) stored 1 =
      some (Element.restore stored 1 sign_checked (by decide +kernel)) :=
  Element.restore?_eq _ _ _ _

/-- Restoration also rejects a false sign through the existing executable API. -/
theorem restore_rejected : Element.restore? (context := context) stored (-1) = none :=
  Element.restore?_stale _ _ (by rw [sign_checked]; decide +kernel)

private theorem canReduce : context.canReduce = true := by
  rw [context.reduce_checked]
  simp only [context, Context.root_adjoin, Context.clean_adjoin, source_raw, singletonRaw, ← Array.all_toList]
  decide +kernel

private theorem reduced : context.reduce stored = 2 * Sturm.Fixtures.x := by
  rw [Context.reduce, dite_eq_left canReduce]
  simp only [context, Context.root_adjoin, source_raw, stored, singletonRaw, DensePoly.divModMonic]
  decide +kernel

private theorem query_small :
    context.queryPoly (2 * Sturm.Fixtures.x) = 2 * Sturm.Fixtures.x := by
  simp only [Context.queryPoly, context, Context.root_adjoin, source_raw, singletonRaw]
  decide +kernel

theorem reduced_sign : context.signPoly (2 * Sturm.Fixtures.x) = 1 := by
  simpa only [Context.signPoly, query_eq, query_small] using sign_checked

/-- Actual packing reduces the stored input; proof-directed restoration can
reuse the checked sign of that precise remainder. -/
theorem packing_checked :
    Element.ofPoly (context := context) stored =
      Element.restore (2 * Sturm.Fixtures.x) 1 reduced_sign (by decide +kernel) := by
  have checked : context.signPoly (context.reduce stored) = 1 := by
    rw [reduced]
    exact reduced_sign
  simpa only [reduced] using Element.ofPoly_restore stored 1 checked (by decide +kernel)

/-- Packing and literal restoration have different stored representatives. -/
theorem packing_literal : (Element.ofPoly (context := context) stored).polynomial ≠ stored := by
  rw [packing_checked, Element.restore_polynomial]
  simp only [stored]
  decide +kernel

private theorem reduced_head : context.reduce Sturm.Fixtures.p = 0 := by
  rw [Context.reduce, dite_eq_left canReduce]
  simp only [context, Context.root_adjoin, source_raw, singletonRaw, DensePoly.divModMonic]
  decide +kernel

/-- A vanishing input packs to canonical zero through the constant sign path. -/
theorem packing_zero : Element.ofPoly (context := context) Sturm.Fixtures.p = 0 := by
  apply Element.ofPoly_eq_zero
  rw [reduced_head, Context.signPoly_const context 0 (by decide +kernel)]
  decide +kernel

/-- info: 'Hex.RealClosure.Algebraic.CoefficientSignsConformance.sign_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_checked

end Hex.RealClosure.Algebraic.CoefficientSignsConformance
