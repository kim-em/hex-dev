/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.TransportClosedQuery
public import HexRealClosureTheory.TransportReduction

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Add E] [Sub E] [Mul E] [One E] [NatCast E] [CommRing K] [DecidableEq K]

omit [DecidableEq K] in
/-- Finite stored memberships supply every product-reduction intermediate. -/
theorem ProductIdentity.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p prev factor next : Hex.DensePoly E) (left : E) (quotient : Hex.DensePoly E) (right : E)
    (hp : ∀ i < p.size, S (p.coeff i)) (ha : ∀ i < prev.size, S (prev.coeff i))
    (hf : ∀ i < factor.size, S (factor.coeff i)) (hn : ∀ i < next.size, S (next.coeff i))
    (hl : S left) (hq : ∀ i < quotient.size, S (quotient.coeff i)) (hr : S right) :
    ProductIdentity read p prev factor next left quotient right := by
  have input := fun i (_ : i < (prev * factor).size) => data.coeff_mul read S prev factor ha hf i
  have product := fun i (_ : i < (quotient * p).size) => data.coeff_mul read S quotient p hq hp i
  have scaled := fun i (_ : i < (Hex.DensePoly.scale right next).size) =>
    data.coeff_scale read S right next hr hn i
  exact ⟨Product.of_closed read S data prev factor ha hf,
    Scaling.of_closed read S data left _ hl input,
    Product.of_closed read S data quotient p hq hp,
    Scaling.of_closed read S data right next hr hn,
    Sum.of_closed read S data _ _ product scaled,
    Difference.of_closed read S data _ _
      (fun i _ => data.coeff_scale read S left _ hl input i)
      (fun i _ => data.coeff_add read S _ _ product scaled i)⟩

/-- Membership of the literal next representative, scales and quotient of a step. -/
structure ReductionDomain (S : E → Prop) (s : Hex.SignDet.ReductionStep E) : Prop where
  next : ∀ i < s.next.size, S (s.next.coeff i)
  left : S s.witness.leftScale
  right : S s.witness.rightScale
  quotient : ∀ i < s.witness.quotient.size, S (s.witness.quotient.coeff i)

/-- Agreement only at the two scales actually queried by one reduction step. -/
structure ReductionSigns (read : E → K) (sourceSign : E → Int) (targetSign : K → Int)
    (s : Hex.SignDet.ReductionStep E) : Prop where
  left : targetSign (read s.witness.leftScale) = sourceSign s.witness.leftScale
  right : targetSign (read s.witness.rightScale) = sourceSign s.witness.rightScale

omit [DecidableEq K] in
/-- Closure derives the whole reduction's arithmetic from finite stored data.
The head guard and exact scale signs are the remaining checker premises. -/
theorem ReductionData.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (sourceSign : E → Int) (targetSign : K → Int) (p prev : Hex.DensePoly E)
    (fs : List (Nat × Hex.DensePoly E)) (ss : List (Hex.SignDet.ReductionStep E))
    (result : Hex.DensePoly E) (head : Leading read p)
    (hp : ∀ i < p.size, S (p.coeff i)) (ha : ∀ i < prev.size, S (prev.coeff i))
    (hf : ∀ pair ∈ fs, ∀ i < pair.2.size, S (pair.2.coeff i))
    (hs : ∀ s ∈ ss, ReductionDomain S s)
    (signs : ∀ s ∈ ss, ReductionSigns read sourceSign targetSign s)
    (hr : ∀ i < result.size, S (result.coeff i)) :
    ReductionData read sourceSign targetSign p prev fs ss result := by
  induction fs generalizing prev ss with
  | nil =>
    cases ss with
    | nil => exact Difference.of_closed read S data prev result ha hr
    | cons s ss => exact trivial
  | cons pair fs ih =>
    cases ss with
    | nil => exact trivial
    | cons s ss =>
      have member : s ∈ s :: ss := by simp
      have domain := hs s member
      have scaleSigns := signs s member
      refine ⟨⟨head, ?_, scaleSigns.left, scaleSigns.right⟩, ?_⟩
      · exact ProductIdentity.of_closed read S data p prev pair.2 s.next _ _ _ hp ha
          (hf pair (by simp)) domain.next domain.left domain.quotient domain.right
      · exact ih s.next ss domain.next
          (fun pair member => hf pair (List.mem_cons_of_mem _ member))
          (fun step member => hs step (List.mem_cons_of_mem _ member))
          (fun step member => signs step (List.mem_cons_of_mem _ member))

omit [Add E] [Sub E] [Mul E] [One E] [NatCast E] in
/-- Factor repetition retains membership of the original query's coefficients. -/
theorem factors_closed (S : E → Prop) (qs : List (Hex.DensePoly E)) (es : List Nat)
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i)) :
    ∀ pair ∈ Hex.SignDet.factors qs es, ∀ i < pair.2.size, S (pair.2.coeff i) := by
  intro pair member
  obtain ⟨⟨⟨q, k⟩, n⟩, indexed, repeated⟩ := List.mem_flatMap.mp member
  have equal : pair = (n, q) := (List.mem_replicate.mp repeated).2
  rw [equal]
  have zipped : (q, k) ∈ qs.zip es :=
    List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp indexed)
  exact members q (List.of_mem_zip zipped).1

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.ProductIdentity.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.ProductIdentity.of_closed
/-- info: 'Hex.RealClosure.Transport.ReductionData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.ReductionData.of_closed
/-- info: 'Hex.RealClosure.Transport.factors_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.factors_closed
