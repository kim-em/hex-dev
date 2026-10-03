/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed
public import HexRealClosureMathlib.SelectedRoot
public meta import HexSturm.Basic

public section

namespace RealClosureConsumer

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

attribute [local instance 2000] Field.toGrindField

noncomputable section

/-- Consume the prepared-query theorem at the ordinary real field. Preparation
and its sign binding remain explicit; this is not a producer-success premise. -/
theorem prepared_count (domain : Sturm.PreparedDomain ℝ)
    (binding : domain.sign = Sturm.orderSign) :
    Sturm.countPrepared domain =
      (Tarski.rootsIn (interpret id (fun _ => Iff.rfl) domain.head)
        (domain.lower.map id) (domain.upper.map id)).card := by
  exact HexSturmMathlib.countPrepared_sound id (fun _ => Iff.rfl)
    rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign HexSturmMathlib.orderSign_eq (fun _ => rfl) (fun _ => rfl)
    domain binding

/-- An accepted arbitrary certificate establishes the lawful domain as well as
the root sum; no assumption that the certificate came from the builder. -/
theorem checked_query (p q : DensePoly ℝ) (a b : Endpoint ℝ) (value : Int)
    (certificate : TarskiCertificate ℝ ℝ Nat)
    (accepted : Sturm.check Sturm.orderSign 7 p q a b value certificate = true) :
    HexSturmMathlib.Domain id (fun _ => Iff.rfl) p a b ∧
      value = Tarski.rootSum (interpret id (fun _ => Iff.rfl) p)
        (interpret id (fun _ => Iff.rfl) q) (a.map id) (b.map id) := by
  exact HexSturmMathlib.check_sound id (fun _ => Iff.rfl)
    rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign HexSturmMathlib.orderSign_eq 7 p q a b value certificate accepted

def rationalHead : DensePoly Rat := DensePoly.ofCoeffs #[-2, 0, 1]

/- Exercise the actual producer. This runtime guard is a conformance example;
the interpretation theorem below retains its successful-answer hypothesis. -/
#guard Sturm.query Sturm.orderSign rationalHead 1 (.finite (-2)) (.finite 2) == some 2

/-- A successful rational answer counts roots after the public coefficient
embedding into the ordinary real field. -/
theorem rational_roots
    (answer : Sturm.query Sturm.orderSign rationalHead 1
      (.finite (-2)) (.finite 2) = some 2) :
    (Tarski.rootsIn (interpret Hex.RealClosure.ratCast Hex.RealClosure.ratZero rationalHead)
      (.finite (-2)) (.finite 2)).card = 2 := by
  open Hex.RealClosure in
  have sound := HexSturmMathlib.query_count ratCast ratZero ratOne ratAdd ratSub ratMul
    ratNat Sturm.orderSign ratSign (fun q => by simp [ratCast]) (fun q => by simp [ratCast])
    rationalHead (.finite (-2)) (.finite 2) 2 answer
  simp only [Endpoint.map, Hex.RealClosure.ratCast, Rat.cast_neg, Rat.cast_ofNat] at sound
  exact_mod_cast sound.symm

/-- info: 'RealClosureConsumer.prepared_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_count

/-- info: 'RealClosureConsumer.checked_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_query

/-- info: 'RealClosureConsumer.rational_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_roots

end

end RealClosureConsumer
