/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TransportPreparation
public import HexSignDet.MomentReplay

public section

namespace Hex.RealClosure.Transport

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [CommRing K] [DecidableEq K]

omit [DecidableEq K] in
/-- The actual binary-power tree retains coefficient membership at every square
and odd-exponent product, with no source ring laws. -/
theorem Closed.coeff_natPow (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (n : Nat) (coefficients : ∀ i < p.size, S (p.coeff i)) (i : Nat) :
    S ((p.natPow n).coeff i) := by
  induction n using Nat.strongRecOn generalizing p i with
  | ind n ih =>
    rw [Hex.DensePoly.natPow]
    by_cases empty : n = 0
    · rw [ite_eq_left empty]
      exact data.coeff_one read S i
    · rw [ite_eq_right empty]
      have square := fun j (_ : j < (p * p).size) => data.coeff_mul read S p p coefficients coefficients j
      have recursive := fun j => ih (n / 2) (by omega) (p * p) square j
      by_cases even : n % 2 = 0
      · rw [ite_eq_left even]
        exact recursive i
      · rw [ite_eq_right even]
        exact data.coeff_mul read S _ p (fun j _ => recursive j) coefficients i

omit [DecidableEq K] in
/-- A closed domain supplies every finite binary-power arithmetic obligation. -/
theorem PowerData.of_closed (read : E → K) (S : E → Prop) (data : Closed read S)
    (p : Hex.DensePoly E) (n : Nat) (coefficients : ∀ i < p.size, S (p.coeff i)) :
    PowerData read p n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    rw [PowerData]
    by_cases empty : n = 0
    · rw [ite_eq_left empty]
      exact trivial
    · rw [ite_eq_right empty]
      have square := fun i (_ : i < (p * p).size) => data.coeff_mul read S p p coefficients coefficients i
      refine ⟨Product.of_closed read S data p p coefficients coefficients,
        ih (n / 2) (by omega) (p * p) square, ?_⟩
      by_cases even : n % 2 = 0
      · rw [ite_eq_left even]
        exact trivial
      · rw [ite_eq_right even]
        exact Product.of_closed read S data _ p
          (fun i _ => data.coeff_natPow read S (p * p) (n / 2) square i) coefficients

omit [DecidableEq K] in
/-- All coefficients of the actual moment product belong to the closed domain. -/
theorem Closed.coeff_moment (read : E → K) (S : E → Prop) (data : Closed read S)
    (qs : List (Hex.DensePoly E)) (es : List Nat)
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i)) (i : Nat) :
    S ((Hex.SignDet.moment qs es).coeff i) := by
  have fold : ∀ (xs : List (Hex.DensePoly E)) (initial : Hex.DensePoly E),
      (∀ p ∈ xs, ∀ j < p.size, S (p.coeff j)) →
      (∀ j < initial.size, S (initial.coeff j)) →
      ∀ j, S ((xs.foldl (· * ·) initial).coeff j) := by
    intro xs
    induction xs with
    | nil =>
      intro initial _ start j
      exact data.coefficient read S initial start j
    | cons p xs ih =>
      intro initial coefficients start j
      exact ih (initial * p)
        (fun q member => coefficients q (List.mem_cons_of_mem _ member))
        (fun k _ => data.coeff_mul read S initial p start (coefficients p (by simp)) k) j
  apply fold _ 1 _ (fun j _ => data.coeff_one read S j) i
  intro p member j _
  obtain ⟨⟨q, k⟩, paired, rfl⟩ := List.mem_map.mp member
  exact data.coeff_natPow read S q k (members q (List.of_mem_zip paired).1) j

private theorem fold_polynomial (read : E → K) (S : E → Prop) (data : Closed read S)
    (xs : List (Hex.DensePoly E)) (members : ∀ p ∈ xs, ∀ i < p.size, S (p.coeff i))
    (initial : Hex.DensePoly E) (start : ∀ i < initial.size, S (initial.coeff i)) :
    polynomial read (xs.foldl (· * ·) initial) =
      (xs.map (polynomial read)).foldl (· * ·) (polynomial read initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons p xs ih =>
    have hp := members p (by simp)
    have product := Product.of_closed read S data initial p start hp
    simp only [List.foldl_cons, List.map_cons]
    rw [ih (fun q member => members q (List.mem_cons_of_mem _ member)) (initial * p)
      (fun i _ => data.coeff_mul read S initial p start hp i),
      Ring.polynomial_mul read data.read_zero initial p product.products product.sums]

/-- Interpretation transports the actual moment's binary powers and product
fold from membership of the finite query coefficients in a closed domain. -/
theorem moment_polynomial (read : E → K) (S : E → Prop) (data : Closed read S)
    (qs : List (Hex.DensePoly E)) (es : List Nat)
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i)) :
    polynomial read (Hex.SignDet.moment qs es) =
      Hex.SignDet.moment (qs.map (polynomial read)) es := by
  have powers : ∀ p ∈ (qs.zip es).map (fun (q, k) => q.natPow k),
      ∀ i < p.size, S (p.coeff i) := by
    intro p member
    obtain ⟨⟨q, k⟩, paired, rfl⟩ := List.mem_map.mp member
    exact fun i _ => data.coeff_natPow read S q k (members q (List.of_mem_zip paired).1) i
  rw [Hex.SignDet.moment, fold_polynomial read S data _ powers 1
    (fun i _ => data.coeff_one read S i), polynomial_one read data.read_zero data.read_one]
  unfold Hex.SignDet.moment
  rw [List.zip_map_left, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair member
  obtain ⟨q, k⟩ := pair
  exact polynomial_natPow read data.read_zero data.read_one q k
    (PowerData.of_closed read S data q k (members q (List.of_mem_zip member).1))

/-- The complete moment checker retains its exponent positions, optional
product reduction, literal Tarski query, context binding and integer value. -/
theorem moment_check {C : Type w} {D : Type z} [DecidableEq C] [DecidableEq D]
    (read : E → K) (S : E → Prop) (closed : Closed read S) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (p : Hex.DensePoly E) (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E)) (es : List Nat)
    (value : Int) (cert : Hex.TarskiCertificate E E C)
    (reduced : Option (Hex.SignDet.Reduction E))
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i))
    (reductions : ∀ r, reduced = some r →
      ReductionData read sourceSign targetSign p 1 (Hex.SignDet.factors qs es) r.steps r.result)
    (data : QueryData read sourceSign targetSign p (Hex.SignDet.queryPoly qs es reduced) a b cert)
    (accepted : Hex.SignDet.checkMoment sourceSign context p a b qs es value cert reduced = true) :
    Hex.SignDet.checkMoment targetSign (contextMap context) (polynomial read p)
      (endpoint read a) (endpoint read b) (qs.map (polynomial read)) es value
      (query read contextMap cert) (reduced.map (reduction read)) = true := by
  have operand : polynomial read (Hex.SignDet.queryPoly qs es reduced) =
      Hex.SignDet.queryPoly (qs.map (polynomial read)) es (reduced.map (reduction read)) := by
    cases reduced with
    | none => exact moment_polynomial read S closed qs es members
    | some r => rfl
  simp only [Hex.SignDet.checkMoment_eq, Bool.and_eq_true] at accepted ⊢
  refine ⟨?_, ?_⟩
  · cases reduced with
    | none => simpa only [Option.map_none, List.length_map] using accepted.1
    | some r =>
      exact reduction_check read closed.read_zero closed.read_one
        sourceSign targetSign p qs es r data.squarefree.head (reductions r rfl) accepted.1
  · rw [← operand]
    exact query_check read closed.read_zero closed.read_one contextMap sourceSign targetSign context
      p (Hex.SignDet.queryPoly qs es reduced) a b value cert data accepted.2

end Hex.RealClosure.Transport

/-- info: 'Hex.RealClosure.Transport.Closed.coeff_natPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_natPow
/-- info: 'Hex.RealClosure.Transport.Closed.coeff_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Closed.coeff_moment
/-- info: 'Hex.RealClosure.Transport.PowerData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.PowerData.of_closed
/-- info: 'Hex.RealClosure.Transport.moment_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.moment_polynomial
/-- info: 'Hex.RealClosure.Transport.moment_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.moment_check
