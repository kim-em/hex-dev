/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportTarski
public import HexSignDet.Reduction

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [CommRing K] [DecidableEq K]

/-- Normalization of interpreted coefficients can only shorten the source array. -/
theorem polynomial_size_le (read : E → K) (p : Hex.DensePoly E) :
    (polynomial read p).size ≤ p.size := by
  simpa only [polynomial, Array.size_map, Hex.DensePoly.toArray_size] using
    Hex.DensePoly.size_ofCoeffs_le (p.toArray.map read)

/-- Interpreting coefficients cannot increase degree, including zero images. -/
theorem polynomial_degree_le (read : E → K) (p : Hex.DensePoly E) :
    (polynomial read p).natDegree ≤ p.natDegree := by
  simp only [Hex.DensePoly.natDegree_eq_size_sub_one]
  exact Nat.sub_le_sub_right (polynomial_size_le read p) 1

/-- Interpret the exact stored factor index, next remainder and witness. -/
@[expose] def reductionStep (read : E → K) (s : Hex.SignDet.ReductionStep E) :
    Hex.SignDet.ReductionStep K :=
  ⟨s.index, polynomial read s.next, step read s.witness⟩

variable [Add E] [Sub E] [Mul E]

/-- The finite native arithmetic in a positive-scaled product reduction. -/
structure ProductIdentity (read : E → K) (p prev factor next : Hex.DensePoly E)
    (left : E) (quotient : Hex.DensePoly E) (right : E) : Prop where
  inputProduct : Product read prev factor
  leftScale : Scaling read left (prev * factor)
  quotientProduct : Product read quotient p
  rightScale : Scaling read right next
  remainder : Sum read (quotient * p) (Hex.DensePoly.scale right next)
  identity : Difference read (Hex.DensePoly.scale left (prev * factor))
    (quotient * p + Hex.DensePoly.scale right next)

/-- The accepted product identity transports the actual finite scalar work,
without leading guards on the product, quotient or next representative. -/
theorem ProductIdentity.zero (read : E → K) (zero : read 0 = 0)
    (p prev factor next : Hex.DensePoly E) (left : E) (quotient : Hex.DensePoly E) (right : E)
    (data : ProductIdentity read p prev factor next left quotient right)
    (accepted : (Hex.DensePoly.scale left (prev * factor) -
      (quotient * p + Hex.DensePoly.scale right next)).isZero = true) :
    (Hex.DensePoly.scale (read left) (polynomial read prev * polynomial read factor) -
      (polynomial read quotient * polynomial read p +
        Hex.DensePoly.scale (read right) (polynomial read next))).isZero = true := by
  have mapped := data.identity.zero read zero _ _ accepted
  rw [Ring.polynomial_scale read zero left _ data.leftScale.products,
    Ring.polynomial_mul read zero prev factor data.inputProduct.products data.inputProduct.sums,
    Ring.polynomial_add read zero _ _ data.remainder.sums,
    Ring.polynomial_mul read zero quotient p data.quotientProduct.products data.quotientProduct.sums,
    Ring.polynomial_scale read zero right next data.rightScale.products] at mapped
  exact mapped

/-- Exactly the finite product identity and two scale signs required by a step.
Only the root head needs its degree retained. -/
structure ReductionStepData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p prev factor : Hex.DensePoly E) (s : Hex.SignDet.ReductionStep E) : Prop where
  head : Leading read p
  identity : ProductIdentity read p prev factor s.next
    s.witness.leftScale s.witness.quotient s.witness.rightScale
  left : targetSign (read s.witness.leftScale) = sourceSign s.witness.leftScale
  right : targetSign (read s.witness.rightScale) = sourceSign s.witness.rightScale

/-- Preserve the full indexed reduction-step check, including its strict degree
bound when the interpreted next remainder shrinks or becomes zero. -/
theorem reduction_step_check (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int) (p prev factor : Hex.DensePoly E)
    (index : Nat) (s : Hex.SignDet.ReductionStep E)
    (data : ReductionStepData read sourceSign targetSign p prev factor s)
    (accepted : s.check sourceSign p prev factor index = true) :
    (reductionStep read s).check targetSign (polynomial read p)
      (polynomial read prev) (polynomial read factor) index = true := by
  obtain ⟨binding, left, right, bound, identity⟩ := Hex.SignDet.ReductionStep.check_eq accepted
  change (decide (s.index = index) &&
    decide (targetSign (read s.witness.leftScale) = 1) &&
    decide (targetSign (read s.witness.rightScale) = 1) &&
    ((polynomial read s.next).isZero ||
      decide ((polynomial read s.next).natDegree < (polynomial read p).natDegree)) &&
    Hex.SignedRemainderChain.subIsZero
      (Hex.DensePoly.scale (read s.witness.leftScale) (polynomial read prev * polynomial read factor))
      (polynomial read s.witness.quotient * polynomial read p +
        Hex.DensePoly.scale (read s.witness.rightScale) (polynomial read s.next))) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨binding, ?_, ?_, ?_, ?_⟩
  · rw [data.left]
    exact left
  · rw [data.right]
    exact right
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    rcases bound with empty | less
    · left
      have source : s.next = 0 := (Hex.DensePoly.size_eq_zero_iff _).mp
        ((Hex.DensePoly.isZero_eq_true_iff _).mp empty)
      rw [source, (polynomial_zero read zero 0 (by simp)).mpr rfl]
      rfl
    · right
      rw [polynomial_degree read zero p data.head]
      exact lt_of_le_of_lt (polynomial_degree_le read s.next) less
  · exact data.identity.zero read zero p prev factor s.next _ _ _ identity

/-- Interpret the exact ordered reduction steps and declared result. -/
@[expose] def reduction (read : E → K) (r : Hex.SignDet.Reduction E) : Hex.SignDet.Reduction K :=
  ⟨r.steps.map (reductionStep read), polynomial read r.result⟩

/-- The finite arithmetic premises along the actual matched factor/step list,
including the final zero difference. Malformed list lengths still fail checking. -/
@[expose] def ReductionData (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (p prev : Hex.DensePoly E) : List (Nat × Hex.DensePoly E) →
      List (Hex.SignDet.ReductionStep E) → Hex.DensePoly E → Prop
  | [], [], result => Difference read prev result
  | (_, factor) :: fs, s :: ss, result =>
    ReductionStepData read sourceSign targetSign p prev factor s ∧
      ReductionData read sourceSign targetSign p s.next fs ss result
  | _, _, _ => True

/-- Preserve every matched factor and step and the final native zero difference.
Duplicate indexed factors remain in the same positions and order. -/
theorem reduction_from_check (read : E → K) (zero : read 0 = 0)
    (sourceSign : E → Int) (targetSign : K → Int) (p prev : Hex.DensePoly E)
    (fs : List (Nat × Hex.DensePoly E)) (ss : List (Hex.SignDet.ReductionStep E))
    (result : Hex.DensePoly E) (data : ReductionData read sourceSign targetSign p prev fs ss result)
    (accepted : Hex.SignDet.Reduction.checkFrom sourceSign p prev fs ss result = true) :
    Hex.SignDet.Reduction.checkFrom targetSign (polynomial read p) (polynomial read prev)
      (fs.map (fun pair => (pair.1, polynomial read pair.2)))
      (ss.map (reductionStep read)) (polynomial read result) = true := by
  induction fs generalizing prev ss with
  | nil =>
    cases ss with
    | nil => exact data.zero read zero prev result accepted
    | cons s ss => simp only [Hex.SignDet.Reduction.checkFrom, Bool.false_eq_true] at accepted
  | cons pair fs ih =>
    obtain ⟨i, factor⟩ := pair
    cases ss with
    | nil => simp only [Hex.SignDet.Reduction.checkFrom, Bool.false_eq_true] at accepted
    | cons s ss =>
      simp only [Hex.SignDet.Reduction.checkFrom, Bool.and_eq_true] at accepted
      simp only [List.map_cons, Hex.SignDet.Reduction.checkFrom, Bool.and_eq_true]
      exact ⟨reduction_step_check read zero sourceSign targetSign p prev factor i s data.1 accepted.1,
        ih s.next ss data.2 accepted.2⟩

omit [Add E] [Sub E] [Mul E] in
/-- Factor interpretation retains indexed duplicates and exponent repetitions. -/
theorem factors_map (read : E → K) (qs : List (Hex.DensePoly E)) (es : List Nat) :
    Hex.SignDet.factors (qs.map (polynomial read)) es =
      (Hex.SignDet.factors qs es).map (fun pair => (pair.1, polynomial read pair.2)) := by
  simp only [Hex.SignDet.factors, List.zip_map_left, List.zipIdx_map, List.flatMap_map,
    List.map_flatMap, List.map_replicate, Prod.map, id_eq]

variable [One E]

/-- The complete reduced-moment checker transports finite arithmetic and signs,
retaining its positive-degree head, exponent guards and declared result. -/
theorem reduction_check (read : E → K) (zero : read 0 = 0) (one : read 1 = 1)
    (sourceSign : E → Int) (targetSign : K → Int) (p : Hex.DensePoly E)
    (qs : List (Hex.DensePoly E)) (es : List Nat) (r : Hex.SignDet.Reduction E)
    (head : Leading read p)
    (data : ReductionData read sourceSign targetSign p 1 (Hex.SignDet.factors qs es) r.steps r.result)
    (accepted : r.check sourceSign p qs es = true) :
    (reduction read r).check targetSign (polynomial read p) (qs.map (polynomial read)) es = true := by
  have source := accepted
  simp only [Hex.SignDet.Reduction.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at source
  simp only [Hex.SignDet.Reduction.check, reduction, polynomial_degree read zero p head,
    List.length_map, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨source.1, source.2.1, source.2.2.1, ?_⟩
  rw [factors_map, ← polynomial_one read zero one]
  exact reduction_from_check read zero sourceSign targetSign p 1
    (Hex.SignDet.factors qs es) r.steps r.result data source.2.2.2

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.polynomial_degree_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.polynomial_degree_le
/-- info: 'Hex.RealClosure.Transport.ProductIdentity.zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.ProductIdentity.zero
/-- info: 'Hex.RealClosure.Transport.reduction_step_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.reduction_step_check

/-- info: 'Hex.RealClosure.Transport.reduction_from_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.reduction_from_check
/-- info: 'Hex.RealClosure.Transport.factors_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.factors_map
/-- info: 'Hex.RealClosure.Transport.reduction_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.reduction_check
