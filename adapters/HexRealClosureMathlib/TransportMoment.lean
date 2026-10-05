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

/-- Finite arithmetic obligations along the actual left-associated product fold. -/
@[expose] def FoldData (read : E → K) : List (Hex.DensePoly E) → Hex.DensePoly E → Prop
  | [], _ => True
  | p :: ps, initial => Product read initial p ∧ FoldData read ps (initial * p)

/-- Interpret a product fold from the reached multiplications alone. -/
theorem FoldData.polynomial (read : E → K) (zero : read 0 = 0)
    (xs : List (Hex.DensePoly E)) (initial : Hex.DensePoly E)
    (data : FoldData read xs initial) :
    polynomial read (xs.foldl (· * ·) initial) =
      (xs.map (polynomial read)).foldl (· * ·) (polynomial read initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons p ps ih =>
    simp only [FoldData] at data
    simp only [List.foldl_cons, List.map_cons]
    rw [ih (initial * p) data.2,
      Ring.polynomial_mul read zero initial p data.1.products data.1.sums]

/-- The actual moment's finite binary-power trees and product fold. -/
structure MomentData (read : E → K) (qs : List (Hex.DensePoly E)) (es : List Nat) : Prop where
  powers : ∀ pair ∈ qs.zip es, PowerData read pair.1 pair.2
  products : FoldData read ((qs.zip es).map (fun (q, k) => q.natPow k)) 1

/-- A closed arithmetic domain supplies the finite fold data as a corollary. -/
theorem FoldData.of_closed (read : E → K) (S : E → Prop) (closed : Closed read S)
    (xs : List (Hex.DensePoly E)) (members : ∀ p ∈ xs, ∀ i < p.size, S (p.coeff i))
    (initial : Hex.DensePoly E) (start : ∀ i < initial.size, S (initial.coeff i)) :
    FoldData read xs initial := by
  induction xs generalizing initial with
  | nil => exact trivial
  | cons p ps ih =>
    have hp := members p (by simp)
    exact ⟨Product.of_closed read S closed initial p start hp,
      ih (fun q member => members q (List.mem_cons_of_mem _ member)) (initial * p)
        (fun i _ => closed.coeff_mul read S initial p start hp i)⟩

/-- Membership in a closed domain derives the reached finite moment operations. -/
theorem MomentData.of_closed (read : E → K) (S : E → Prop) (closed : Closed read S)
    (qs : List (Hex.DensePoly E)) (es : List Nat)
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i)) : MomentData read qs es := by
  refine ⟨?_, ?_⟩
  · intro pair member
    exact PowerData.of_closed read S closed pair.1 pair.2
      (members pair.1 (List.of_mem_zip member).1)
  · apply FoldData.of_closed read S closed _ _ 1 (fun i _ => closed.coeff_one read S i)
    intro p member i _
    obtain ⟨⟨q, k⟩, paired, rfl⟩ := List.mem_map.mp member
    exact closed.coeff_natPow read S q k (members q (List.of_mem_zip paired).1) i

namespace Finite

/-- Moment interpretation requires only the reached power and product operations. -/
theorem moment_polynomial (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1)
    (qs : List (Hex.DensePoly E)) (es : List Nat) (data : MomentData read qs es) :
    polynomial read (Hex.SignDet.moment qs es) =
      Hex.SignDet.moment (qs.map (polynomial read)) es := by
  rw [Hex.SignDet.moment, FoldData.polynomial read zero _ 1 data.products,
    polynomial_one read zero unit]
  unfold Hex.SignDet.moment
  rw [List.zip_map_left, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro pair member
  exact polynomial_natPow read zero unit pair.1 pair.2 (data.powers pair member)

/-- Transport the actual optional reduction and Tarski moment check from finite
operations, without closure over arbitrary pairs of domain elements. -/
theorem moment_check {C : Type w} {D : Type z} [DecidableEq C] [DecidableEq D]
    (read : E → K) (zero : read 0 = 0) (unit : read 1 = 1) (contextMap : C → D)
    (sourceSign : E → Int) (targetSign : K → Int) (context : C)
    (p : Hex.DensePoly E) (a b : Hex.Endpoint E) (qs : List (Hex.DensePoly E)) (es : List Nat)
    (value : Int) (cert : Hex.TarskiCertificate E E C)
    (reduced : Option (Hex.SignDet.Reduction E))
    (products : reduced = none → MomentData read qs es)
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
    | none => exact moment_polynomial read zero unit qs es (products rfl)
    | some r => rfl
  simp only [Hex.SignDet.checkMoment_eq, Bool.and_eq_true] at accepted ⊢
  refine ⟨?_, ?_⟩
  · cases reduced with
    | none => simpa only [Option.map_none, List.length_map] using accepted.1
    | some r =>
      exact reduction_check read zero unit sourceSign targetSign p qs es r
        data.squarefree.head (reductions r rfl) accepted.1
  · rw [← operand]
    exact query_check read zero unit contextMap sourceSign targetSign context
      p (Hex.SignDet.queryPoly qs es reduced) a b value cert data accepted.2

end Finite

/-- Interpretation transports the actual moment's binary powers and product
fold from membership of the finite query coefficients in a closed domain. -/
theorem moment_polynomial (read : E → K) (S : E → Prop) (data : Closed read S)
    (qs : List (Hex.DensePoly E)) (es : List Nat)
    (members : ∀ q ∈ qs, ∀ i < q.size, S (q.coeff i)) :
    polynomial read (Hex.SignDet.moment qs es) =
      Hex.SignDet.moment (qs.map (polynomial read)) es := by
  exact Finite.moment_polynomial read data.read_zero data.read_one qs es
    (MomentData.of_closed read S data qs es members)


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
  exact Finite.moment_check read closed.read_zero closed.read_one contextMap
    sourceSign targetSign context p a b qs es value cert reduced
    (fun _ => MomentData.of_closed read S closed qs es members) reductions data accepted

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

/-- info: 'Hex.RealClosure.Transport.FoldData.polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.FoldData.polynomial

/-- info: 'Hex.RealClosure.Transport.FoldData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.FoldData.of_closed

/-- info: 'Hex.RealClosure.Transport.MomentData.of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.MomentData.of_closed

/-- info: 'Hex.RealClosure.Transport.Finite.moment_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.moment_polynomial

/-- info: 'Hex.RealClosure.Transport.Finite.moment_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Transport.Finite.moment_check
