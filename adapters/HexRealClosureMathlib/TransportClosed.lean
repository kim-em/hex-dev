/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportTarski

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [Add E] [Mul E] [Sub E] [One E] [NatCast E]
variable [CommRing K] [DecidableEq K]

/-- A domain on which interpretation preserves arithmetic. Closure supplies
membership of reached accumulators; no equation outside this domain is required. -/
structure Closed (read : E → K) (S : E → Prop) : Prop where
  zero : S 0
  add : ∀ a b, S a → S b → S (a + b)
  mul : ∀ a b, S a → S b → S (a * b)
  sub : ∀ a b, S a → S b → S (a - b)
  one : S 1
  natCast : ∀ n : Nat, S (n : E)
  read_zero : read 0 = 0
  read_add : ∀ a b, S a → S b → read (a + b) = read a + read b
  read_mul : ∀ a b, S a → S b → read (a * b) = read a * read b
  read_sub : ∀ a b, S a → S b → read (a - b) = read a - read b
  read_one : read 1 = 1
  read_natCast : ∀ n : Nat, read (n : E) = (n : K)

omit [DecidableEq K] in
theorem Closed.coefficient (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (coefficients : ∀ i < p.size, S (p.coeff i)) (i : Nat) :
    S (p.coeff i) := by
  by_cases bound : i < p.size
  · exact coefficients i bound
  · rw [Hex.DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt bound)]
    exact data.zero

omit [Zero E] [DecidableEq E] [Add E] [Mul E] [Sub E] [One E] [NatCast E] [CommRing K] [DecidableEq K] in
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
private theorem array_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (cs : Array E) (members : ∀ c ∈ cs, S c) (i : Nat) :
    S ((Hex.DensePoly.ofCoeffs cs).coeff i) := by
  rw [Hex.DensePoly.coeff_ofCoeffs]
  by_cases bound : i < cs.size
  · rw [← Array.getElem_eq_getD (h := bound) (Zero.zero : E)]
    exact members cs[i] (Array.getElem_mem bound)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_gt bound)]
    simp only [Option.getD_none]
    exact data.zero

omit [DecidableEq K] in
/-- The stored unit polynomial has coefficients in every closed domain. -/
theorem Closed.coeff_one (read : E → K) (S : E → Prop) (data : Closed read S) (i : Nat) :
    S ((1 : Hex.DensePoly E).coeff i) := by
  change S ((Hex.DensePoly.C (1 : E)).coeff i)
  rw [Hex.DensePoly.coeff_C]
  split
  · exact data.one
  · exact data.zero

omit [DecidableEq K] in
/-- Membership of every product coefficient follows the native nested folds. -/
theorem Closed.coeff_mul (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E) (first : ∀ i < p.size, S (p.coeff i))
    (second : ∀ i < q.size, S (q.coeff i)) (n : Nat) : S ((p * q).coeff n) := by
  rw [Hex.DensePoly.coeff_mul, Hex.DensePoly.mulCoeffSum]
  apply foldl_closed S _ _ (fun acc i _ ha => ?_) 0 data.zero
  apply foldl_closed S _ _ (fun acc j _ ha => ?_) acc ha
  unfold Hex.DensePoly.mulCoeffStep
  split
  · exact data.add _ _ ha (data.mul _ _
      (data.coefficient read S p first i) (data.coefficient read S q second j))
  · exact ha

omit [DecidableEq K] in
/-- Scaling retains coefficient membership, including implicit zero entries. -/
theorem Closed.coeff_scale (read : E → K) (S : E → Prop) (data : Closed read S)
    (c : E) (p : Hex.DensePoly E) (scalar : S c)
    (coefficients : ∀ i < p.size, S (p.coeff i)) (n : Nat) :
    S ((Hex.DensePoly.scale c p).coeff n) := by
  rw [Hex.DensePoly.scale_eq_scaleImpl, Hex.DensePoly.scaleImpl]
  apply array_closed read S data
  intro a member
  obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp member
  rw [← equal, Array.getElem_map]
  apply data.mul _ _ scalar
  rw [Array.getElem_eq_getD (h := by simpa using hi) (Zero.zero : E)]
  exact coefficients i (by simpa using hi)

omit [DecidableEq K] in
/-- Addition retains membership without requiring source ring laws. -/
theorem Closed.coeff_add (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E) (first : ∀ i < p.size, S (p.coeff i))
    (second : ∀ i < q.size, S (q.coeff i)) (n : Nat) : S ((p + q).coeff n) := by
  change S ((Hex.DensePoly.add p q).coeff n)
  rw [Hex.DensePoly.add_eq_addImpl, Hex.DensePoly.addImpl]
  apply array_closed read S data
  intro a member
  obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp member
  rw [← equal, Array.getElem_ofFn]
  exact data.add _ _ (data.coefficient read S p first i) (data.coefficient read S q second i)

omit [DecidableEq K] in
/-- Subtraction retains membership through the executable coefficient array. -/
theorem Closed.coeff_sub (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E) (first : ∀ i < p.size, S (p.coeff i))
    (second : ∀ i < q.size, S (q.coeff i)) (n : Nat) : S ((p - q).coeff n) := by
  change S ((Hex.DensePoly.sub p q).coeff n)
  rw [Hex.DensePoly.sub_eq_subImpl, Hex.DensePoly.subImpl]
  apply array_closed read S data
  intro a member
  obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp member
  rw [← equal, Array.getElem_ofFn]
  exact data.sub _ _ (data.coefficient read S p first i) (data.coefficient read S q second i)

omit [DecidableEq K] in
/-- Derivatives use only natural casts and coefficients already in the domain. -/
theorem Closed.coeff_derivative (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (coefficients : ∀ i < p.size, S (p.coeff i)) (n : Nat) :
    S (p.derivative.coeff n) := by
  rw [Hex.DensePoly.derivative_eq_derivativeImpl, Hex.DensePoly.derivativeImpl]
  apply array_closed read S data
  intro a member
  obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp member
  rw [← equal, Array.getElem_ofFn]
  exact data.mul _ _ (data.natCast _) (data.coefficient read S p coefficients (i + 1))

omit [DecidableEq K] in
/-- A closed interpretation domain discharges every native multiplication
accumulator obligation from the stored coefficient memberships. -/
theorem Product.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E)
    (first : ∀ i < p.size, S (p.coeff i)) (second : ∀ i < q.size, S (q.coeff i)) :
    Product read p q := by
  have hp i := Closed.coefficient read S data p first i
  have hq j := Closed.coefficient read S data q second j
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
    (coefficients : ∀ i < p.size, S (p.coeff i)) :
    Evaluation read p x := by
  have hp i := Closed.coefficient read S data p coefficients i
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
  exact ⟨fun i hi => data.read_mul _ _ (accumulator i) argument,
    fun i hi => data.read_add _ _ (data.mul _ _ (accumulator i) argument) (hp (p.size - 1 - i))⟩

omit [DecidableEq K] in
/-- Closed-domain membership supplies the finite subtraction equations. -/
theorem Difference.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E) (first : ∀ i < p.size, S (p.coeff i))
    (second : ∀ i < q.size, S (q.coeff i)) : Difference read p q :=
  ⟨fun i _ => data.read_sub _ _ (data.coefficient read S p first i)
    (data.coefficient read S q second i)⟩

omit [DecidableEq K] in
/-- Closed-domain membership supplies the finite addition equations. -/
theorem Sum.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p q : Hex.DensePoly E) (first : ∀ i < p.size, S (p.coeff i))
    (second : ∀ i < q.size, S (q.coeff i)) : Sum read p q :=
  ⟨fun i _ => data.read_add _ _ (data.coefficient read S p first i)
    (data.coefficient read S q second i)⟩

omit [DecidableEq K] in
/-- Closed-domain membership supplies the finite scaling equations. -/
theorem Scaling.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (c : E) (p : Hex.DensePoly E) (scalar : S c)
    (coefficients : ∀ i < p.size, S (p.coeff i)) : Scaling read c p :=
  ⟨fun i _ => data.read_mul _ _ scalar (data.coefficient read S p coefficients i)⟩

omit [DecidableEq K] in
/-- Cast preservation and closure supply the derivative equations. -/
theorem Differentiation.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (coefficients : ∀ i < p.size, S (p.coeff i)) :
    Differentiation read p := by
  refine ⟨fun i _ => ?_⟩
  rw [data.read_mul _ _ (data.natCast _) (data.coefficient read S p coefficients (i + 1)),
    data.read_natCast]

omit [DecidableEq K] in
/-- Membership of the stored operands and scales supplies the whole recurrence. -/
theorem Recurrence.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (a b c : Hex.DensePoly E) (left : E) (quotient : Hex.DensePoly E) (right : E)
    (ha : ∀ i < a.size, S (a.coeff i)) (hb : ∀ i < b.size, S (b.coeff i))
    (hc : ∀ i < c.size, S (c.coeff i)) (hl : S left)
    (hq : ∀ i < quotient.size, S (quotient.coeff i)) (hr : S right) :
    Recurrence read a b c left quotient right := by
  have product := fun i (_ : i < (quotient * b).size) => data.coeff_mul read S quotient b hq hb i
  have scaled := fun i (_ : i < (Hex.DensePoly.scale right c).size) =>
    data.coeff_scale read S right c hr hc i
  exact ⟨Scaling.of_closed read S data left a hl ha,
    Product.of_closed read S data quotient b hq hb,
    Scaling.of_closed read S data right c hr hc,
    Difference.of_closed read S data _ _ product scaled,
    Difference.of_closed read S data _ _
      (fun i _ => data.coeff_scale read S left a hl ha i)
      (fun i _ => data.coeff_sub read S _ _ product scaled i)⟩

omit [DecidableEq K] in
/-- Membership of literal initial data supplies differentiation and all intermediates. -/
theorem Initial.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p f c : Hex.DensePoly E) (left : E) (quotient : Hex.DensePoly E) (right : E)
    (hp : ∀ i < p.size, S (p.coeff i)) (hf : ∀ i < f.size, S (f.coeff i))
    (hc : ∀ i < c.size, S (c.coeff i)) (hl : S left)
    (hq : ∀ i < quotient.size, S (quotient.coeff i)) (hr : S right) :
    Initial read p f c left quotient right := by
  have derivative := fun i (_ : i < p.derivative.size) => data.coeff_derivative read S p hp i
  have input := fun i (_ : i < (f * p.derivative).size) =>
    data.coeff_mul read S f p.derivative hf derivative i
  have product := fun i (_ : i < (quotient * p).size) => data.coeff_mul read S quotient p hq hp i
  have scaled := fun i (_ : i < (Hex.DensePoly.scale right c).size) =>
    data.coeff_scale read S right c hr hc i
  exact ⟨Differentiation.of_closed read S data p hp,
    Product.of_closed read S data f p.derivative hf derivative,
    Scaling.of_closed read S data left _ hl input,
    Product.of_closed read S data quotient p hq hp,
    Scaling.of_closed read S data right c hr hc,
    Sum.of_closed read S data _ _ product scaled,
    Difference.of_closed read S data _ _
      (fun i _ => data.coeff_scale read S left _ hl input i)
      (fun i _ => data.coeff_add read S _ _ product scaled i)⟩

omit [DecidableEq K] in
/-- Membership of stored terminal data supplies its final divisibility identity. -/
theorem Terminal.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (a b : Hex.DensePoly E) (scale : E) (quotient : Hex.DensePoly E)
    (ha : ∀ i < a.size, S (a.coeff i)) (hb : ∀ i < b.size, S (b.coeff i))
    (hs : S scale) (hq : ∀ i < quotient.size, S (quotient.coeff i)) :
    Terminal read a b scale quotient :=
  ⟨Scaling.of_closed read S data scale a hs ha,
    Product.of_closed read S data quotient b hq hb,
    Difference.of_closed read S data _ _
      (fun i _ => data.coeff_scale read S scale a hs ha i)
      (fun i _ => data.coeff_mul read S quotient b hq hb i)⟩

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.Product.of_closed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Product.of_closed
/-- info: 'Hex.RealClosure.Transport.Evaluation.of_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Evaluation.of_closed

/-- info: 'Hex.RealClosure.Transport.Closed.coefficient' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coefficient
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_mul
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_scale
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_add
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_sub
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_derivative
/-- info: 'Hex.RealClosure.Transport.Difference.of_closed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Difference.of_closed
/-- info: 'Hex.RealClosure.Transport.Sum.of_closed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Sum.of_closed
/-- info: 'Hex.RealClosure.Transport.Scaling.of_closed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Scaling.of_closed
/-- info: 'Hex.RealClosure.Transport.Differentiation.of_closed' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Differentiation.of_closed
/-- info: 'Hex.RealClosure.Transport.Recurrence.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Recurrence.of_closed
/-- info: 'Hex.RealClosure.Transport.Initial.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Initial.of_closed
/-- info: 'Hex.RealClosure.Transport.Terminal.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Terminal.of_closed

/-- info: 'Hex.RealClosure.Transport.Closed.coeff_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_one
