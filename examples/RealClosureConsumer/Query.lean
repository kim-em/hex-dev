/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed
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

@[expose] def realCast : Rat → ℝ := fun q => (q : ℝ)

private theorem cast_sign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (realCast q) : Int) := by
  by_cases hn : q < 0
  · have hn' : realCast q < 0 := by simpa [realCast] using hn
    simp [Sturm.orderSign, hn, sign_eq_neg_one_iff.mpr hn']
  · by_cases hz : q = 0
    · subst q
      simp [Sturm.orderSign, realCast]
    · have hp : 0 < q := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hp' : 0 < realCast q := by simpa [realCast] using hp
      simp [Sturm.orderSign, hn, hz, sign_eq_one_iff.mpr hp']

/- Exercise the actual producer. This runtime guard is a conformance example;
the interpretation theorem below retains its successful-answer hypothesis. -/
#guard Sturm.query Sturm.orderSign rationalHead 1 (.finite (-2)) (.finite 2) == some 2

/-- A successful rational answer counts roots after the public coefficient
embedding into the ordinary real field. -/
theorem rational_roots
    (answer : Sturm.query Sturm.orderSign rationalHead 1
      (.finite (-2)) (.finite 2) = some 2) :
    (Tarski.rootsIn (interpret realCast (fun _ => Rat.cast_eq_zero) rationalHead)
      (.finite (-2)) (.finite 2)).card = 2 := by
  have sound := HexSturmMathlib.query_count realCast (fun _ => Rat.cast_eq_zero)
    (by simp [realCast]) (fun _ _ => by simp [realCast]) (fun _ _ => by simp [realCast])
    (fun _ _ => by simp [realCast]) (fun _ => by simp [realCast])
    Sturm.orderSign cast_sign (fun _ => by simp [realCast]) (fun _ => by simp [realCast])
    rationalHead (.finite (-2)) (.finite 2) 2 answer
  simp only [Endpoint.map, realCast, Rat.cast_neg, Rat.cast_ofNat] at sound
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
