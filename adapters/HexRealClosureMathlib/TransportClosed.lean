/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportTarski

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [Add E] [Mul E]
variable [CommRing K] [DecidableEq K]

/-- A domain on which interpretation preserves arithmetic. Closure supplies
membership of reached accumulators; no equation outside this domain is required. -/
structure Closed (read : E → K) (S : E → Prop) : Prop where
  zero : S 0
  add : ∀ a b, S a → S b → S (a + b)
  mul : ∀ a b, S a → S b → S (a * b)
  read_zero : read 0 = 0
  read_add : ∀ a b, S a → S b → read (a + b) = read a + read b
  read_mul : ∀ a b, S a → S b → read (a * b) = read a * read b

omit [DecidableEq K] in
private theorem coefficient_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (coefficients : ∀ i < p.size, S (p.coeff i)) (i : Nat) :
    S (p.coeff i) := by
  by_cases bound : i < p.size
  · exact coefficients i bound
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt bound)]
    exact data.zero

omit [Zero E] [DecidableEq E] [Add E] [Mul E] [CommRing K] [DecidableEq K] in
private theorem foldl_closed {A : Type w} (S : E → Prop) (step : E → A → E)
    (xs : List A) (closed : ∀ acc a, a ∈ xs → S acc → S (step acc a))
    (initial : E) (start : S initial) :
    S (xs.foldl step initial) := by
  induction xs generalizing initial with
  | nil => exact start
  | cons a xs ih =>
    exact ih (fun acc b hb ha => closed acc b (by simp [hb]) ha)
      (step initial a) (closed initial a (by simp) start)

omit [DecidableEq K] in
/-- A closed interpretation domain discharges every native multiplication
accumulator obligation from the stored coefficient memberships. -/
theorem Product.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E)
    (first : ∀ i < p.size, S (p.coeff i)) (second : ∀ i < q.size, S (q.coeff i)) :
    Product read p q := by
  have hp i := coefficient_closed read S data p first i
  have hq j := coefficient_closed read S data q second j
  have step n i acc j (ha : S acc) : S (Hex.DensePoly.mulCoeffStep p q n i acc j) := by
    unfold Hex.DensePoly.mulCoeffStep
    split
    · exact data.add _ _ ha (data.mul _ _ (hp i) (hq j))
    · exact ha
  have accumulator n i j : S (productPrefix p q n i j) := by
    unfold productPrefix
    apply foldl_closed S _ _ (fun acc j _ ha => step n i acc j ha)
    apply foldl_closed S _ _ (fun acc i _ ha =>
      foldl_closed S _ _ (fun acc j _ ha => step n i acc j ha) acc ha)
    exact data.zero
  refine ⟨?_, ?_⟩
  · intro i hi j hj
    exact data.read_mul _ _ (hp i) (hq j)
  · intro i hi j hj
    exact data.read_add _ _ (accumulator (i + j) i j) (data.mul _ _ (hp i) (hq j))

omit [DecidableEq K] in
/-- Closure also discharges every reached Horner accumulator, rather than
requiring a global homomorphism on the source expression carrier. -/
theorem Evaluation.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (x : E) (argument : S x)
    (coefficients : ∀ i < p.size, S (p.coeff i)) (leading : Leading read p) :
    Evaluation read p x := by
  have hp i := coefficient_closed read S data p coefficients i
  have accumulator i : S (hornerPrefix p x i) := by
    unfold hornerPrefix
    apply foldl_closed S _ _ (fun acc coeff member ha => ?_) 0 data.zero
    have entry : coeff ∈ p.toArray := by
      simpa only [List.mem_reverse, Array.mem_toList_iff] using List.mem_of_mem_take member
    obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp entry
    have hc : S coeff := by
      rw [← equal, Array.getElem_eq_getD (h := hi) (Zero.zero : E)]
      change S (p.coeff i)
      exact coefficients i (by simpa using hi)
    exact data.add _ _ (data.mul _ _ ha argument) hc
  exact ⟨leading, fun i hi => data.read_mul _ _ (accumulator i) argument,
    fun i hi => data.read_add _ _ (data.mul _ _ (accumulator i) argument) (hp (p.size - 1 - i))⟩

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.Product.of_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Product.of_closed
/-- info: 'Hex.RealClosure.Transport.Evaluation.of_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Evaluation.of_closed
