/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSturmMathlib.Soundness
public import HexRealRootsMathlib.RealClosed

public section

namespace RealClosureConsumer

open Hex HexPolyMathlib.Interpret HexRealRootsMathlib

attribute [local instance 2000] Field.toGrindField

noncomputable section

local instance : DecidableEq ℝ := Classical.decEq ℝ

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

/-- info: 'RealClosureConsumer.prepared_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_count

/-- info: 'RealClosureConsumer.checked_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked_query

end

end RealClosureConsumer
