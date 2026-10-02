/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Tests.Replay.Accepted
public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.TarskiReal
public import HexRealRoots.TarskiTests
public import HexRealRootsMathlib.RealClosed
public import HexPoly.InterpretTests

public section

/-! Semantic replay probes for canonical and noninjective representations.
Computational conformance owner: `HexSturm`.
The universal query theorem and each instantiated literal result have only
Lean's standard logical axioms. Acceptance and domain audits also retain that
axiom boundary. -/

namespace HexSturmMathlib.ReplayTests

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

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
      (.finite (HexRealRootsMathlib.Dyadic.toReal Hex.TarskiTests.interval.lower))
      (.finite (HexRealRootsMathlib.Dyadic.toReal Hex.TarskiTests.interval.upper)) :=
  Tarski.integer_check_sound 7 _ _ _ _ _ _ integer_accepted

/-- info: 'HexSturmMathlib.ReplayTests.integer_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integer_value

/-- info: 'HexSturmMathlib.ReplayTests.rational_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_value

/-- info: 'HexSturmMathlib.ReplayTests.literal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms literal_value

/-- info: 'HexSturmMathlib.ReplayTests.noncanonical_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms noncanonical_value

/-- info: 'HexSturmMathlib.countPrepared_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.countPrepared_sound
/-- info: 'HexSturmMathlib.countPrepared_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.countPrepared_nonneg

-- Acceptance and domain proofs retain the same axiom boundary.
/-- info: 'HexSturmMathlib.ReplayTests.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted

/-- info: 'HexSturmMathlib.ReplayTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms domain

/-- info: 'HexRealRootsMathlib.Tarski.integer_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexRealRootsMathlib.Tarski.integer_check_sound

/-- info: 'Hex.ZPoly.tarskiQuery_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.ZPoly.tarskiQuery_eq

/-- info: 'HexSturmMathlib.query_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.query_nonneg

/-- info: 'HexSturmMathlib.rootCount_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.rootCount_eq

/-- info: 'HexSturmMathlib.rootCount_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.rootCount_query

/-- info: 'HexSturmMathlib.rootCount_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.rootCount_map

/-- info: 'HexSturmMathlib.query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.query_bound

/-- info: 'HexSturmMathlib.query_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HexSturmMathlib.query_sign

/-- info: 'HexSturmMathlib.query_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.query_spec

/-- info: 'HexSturmMathlib.rootCount_sturm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexSturmMathlib.rootCount_sturm

end HexSturmMathlib.ReplayTests
