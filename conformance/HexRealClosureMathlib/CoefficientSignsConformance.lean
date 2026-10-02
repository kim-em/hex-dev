/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Algebraic
public import HexRealRootsMathlib.RealClosed
public import HexSignDetMathlib.GraphSignsConformance
public meta import HexRealClosure.Algebraic
public meta import HexSignDet.Conformance

public section

/-! Restore literal algebraic coefficients from supplied lower-level evidence.
The child certificate is checked in the ordinary kernel; no producer runs in
these examples. Cross-level graph serialization is a separate interface. -/
namespace Hex.RealClosure.Algebraic.CoefficientSignsConformance

open Hex.SignDet Hex.SignDet.Conformance
open Hex.SignDetMathlib.GraphSignsConformance
open scoped Hex

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
/-- Supplied evidence must refer to the reduced query in its exact context.
A wrong sign, the unreduced representative or a copied context rejects. -/
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
  rw [HexSturmMathlib.orderSign_eq]
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

/-- info: 'Hex.RealClosure.Algebraic.CoefficientSignsConformance.sign_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sign_checked

end Hex.RealClosure.Algebraic.CoefficientSignsConformance
