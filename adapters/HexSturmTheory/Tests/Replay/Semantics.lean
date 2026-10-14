/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmTheory.Tests.Replay.Accepted
public import HexSturmTheory.Soundness
public import HexRealRootsTheory.TarskiReal
public import HexRealRoots.TarskiTests
public import HexRealRootsTheory.RealClosed
public import HexPoly.InterpretTests

public section

/-! Semantic replay probes for canonical and noninjective representations.
Computational conformance owner: `HexSturm`.
The universal query theorem and each instantiated literal result have only
Lean's standard logical axioms. Acceptance and domain audits also retain that
axiom boundary. -/

namespace HexSturmTheory.ReplayTests

open Hex HexPolyTheory.Interpret HexRealRootsTheory

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- An arbitrary accepted rational certificate has the shared real semantics.
This theorem deliberately has no producer hypothesis. -/
theorem rational_value {Ctx : Type*} [DecidableEq Ctx] (context : Ctx)
    (p q : DensePoly Rat) (a b : Endpoint Rat) (value : Int)
    (certificate : TarskiCertificate Rat Rat Ctx)
    (checked : Sturm.check Sturm.orderSign context p q a b value certificate = true) :
    value = Tarski.rootSum
      (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) p)
      (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) q)
      (a.map (fun r : Rat => (r : ℝ))) (b.map (fun r : Rat => (r : ℝ))) := by
  exact (check_sound (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp)
    Sturm.orderSign rational_sign context p q a b value certificate checked).2

/-- The existing literal replay is connected to real-root semantics. -/
theorem literal_value :
    2 = Tarski.rootSum
      (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) Sturm.Fixtures.p)
      (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) 1)
      (.finite (-2)) (.finite 2) := by
  simpa only [Endpoint.map, Rat.cast_neg, Rat.cast_ofNat] using
    rational_value 7 _ _ _ _ _ _ accepted

open HexPoly.InterpretTests in
/-- Semantic replay also accepts a noninjective representation with only
ordinary coefficient operations, without any field instance on its storage. -/
theorem noncanonical_value {Ctx : Type*} [DecidableEq Ctx] (context : Ctx)
    (p q : Poly) (a b : Endpoint Rep) (v : Int)
    (certificate : TarskiCertificate Rep Rep Ctx)
    (checked : Sturm.check (fun x => Sturm.orderSign (value x))
      context p q a b v certificate = true) :
    v = Tarski.rootSum
      (interpret (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero]) p)
      (interpret (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero]) q)
      (a.map (fun x => (value x : ℝ))) (b.map (fun x => (value x : ℝ))) := by
  exact (check_sound (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero])
    (by simp [value_one]) (fun x y => by simp [value_add])
    (fun x y => by simp [value_sub]) (fun x y => by simp [value_mul])
    (fun n => by simp [value_natCast]) (fun x => Sturm.orderSign (value x))
    (fun x => rational_sign (value x)) context p q a b v certificate checked).2

open HexPoly.InterpretTests in
/-- The full query contract applies to noninjective storage without field or
order instances on that storage, in both directions and without a producer. -/
theorem noncanonical_query_iff (p q : Poly) (a b : Endpoint Rep) (v : Int) :
    Sturm.query (fun x => Sturm.orderSign (value x)) p q a b = some v ↔
      Domain (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero]) p a b ∧
        v = Tarski.rootSum
          (interpret (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero]) p)
          (interpret (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero]) q)
          (a.map (fun x => (value x : ℝ))) (b.map (fun x => (value x : ℝ))) := by
  exact query_iff (fun x => (value x : ℝ)) (fun x => by simp [value_eq_zero])
    (by simp [value_one]) (fun x y => by simp [value_add])
    (fun x y => by simp [value_sub]) (fun x y => by simp [value_mul])
    (fun n => by simp [value_natCast]) (fun x => Sturm.orderSign (value x))
    (fun x => rational_sign (value x)) (fun x => by
      change ((value (pack (-(raw x).1) (-(raw x).2))) : ℝ) = _
      rw [value_pack]
      simp [value, atOne, add_comm])
    (fun x => by simp [value_inv]) p q a b v

/-- Kernel replay with integer coefficients and distinct dyadic endpoint storage. -/
theorem integer_accepted :
    TarskiCertificate.check Int.sign EndpointSigns.intDyadic (7 : Nat)
      Hex.TarskiTests.p 1 (.finite Hex.TarskiTests.interval.lower)
      (.finite Hex.TarskiTests.interval.upper) 2 Hex.TarskiTests.sharedLiteral = true := by
  simp only [TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- The integer/dyadic literal has the same root-sum semantics as the field replay. -/
theorem integer_value :
    2 = Tarski.rootSum (toPolyℝ Hex.TarskiTests.p) (toPolyℝ 1)
      (.finite (HexRealRootsTheory.Dyadic.toReal Hex.TarskiTests.interval.lower))
      (.finite (HexRealRootsTheory.Dyadic.toReal Hex.TarskiTests.interval.upper)) :=
  Tarski.integer_check_sound 7 _ _ _ _ _ _ integer_accepted

/-- info: 'HexSturmTheory.ReplayTests.integer_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integer_value

/-- info: 'HexSturmTheory.ReplayTests.rational_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_value

/-- info: 'HexSturmTheory.ReplayTests.literal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms literal_value

/-- info: 'HexSturmTheory.ReplayTests.noncanonical_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noncanonical_value

/-- info: 'HexSturmTheory.countPrepared_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.countPrepared_sound
/-- info: 'HexSturmTheory.countPrepared_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmTheory.countPrepared_nonneg

-- Acceptance and domain proofs retain the same axiom boundary.
/-- info: 'HexSturmTheory.ReplayTests.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted

/-- info: 'HexSturmTheory.ReplayTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms domain

/-- info: 'HexRealRootsTheory.Tarski.integer_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexRealRootsTheory.Tarski.integer_check_sound

/-- info: 'Hex.ZPoly.tarskiQuery_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.ZPoly.tarskiQuery_eq

/-- info: 'HexSturmTheory.query_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.query_nonneg

/-- info: 'HexSturmTheory.rootCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.rootCount_eq

/-- info: 'HexSturmTheory.rootCount_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.rootCount_query

/-- info: 'HexSturmTheory.rootCount_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.rootCount_map

/-- info: 'HexSturmTheory.query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.query_bound

/-- info: 'HexSturmTheory.query_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmTheory.query_sign

/-- info: 'HexSturmTheory.query_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmTheory.query_spec

/-- info: 'HexSturmTheory.query_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmTheory.query_iff

/-- info: 'HexSturmTheory.ReplayTests.noncanonical_query_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_query_iff

/-- info: 'HexSturmTheory.rootCount_sturm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmTheory.rootCount_sturm

end HexSturmTheory.ReplayTests
