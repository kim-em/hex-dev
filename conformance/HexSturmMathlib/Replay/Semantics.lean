/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Replay.Accepted
public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed
public import HexPoly.InterpretTests

public section

/-! Semantic replay dependencies, separate from the fully proved acceptance probe.
Computational conformance owner: `HexSturm`. -/

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

/-- info: 'HexSturmMathlib.ReplayTests.rational_value' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_value

/-- info: 'HexSturmMathlib.ReplayTests.literal_value' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_value

/-- info: 'HexSturmMathlib.ReplayTests.noncanonical_value' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noncanonical_value

-- Admission of semantic soundness must not contaminate acceptance or domain proofs.
/-- info: 'HexSturmMathlib.ReplayTests.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms accepted

/-- info: 'HexSturmMathlib.ReplayTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms domain

end HexSturmMathlib.ReplayTests
