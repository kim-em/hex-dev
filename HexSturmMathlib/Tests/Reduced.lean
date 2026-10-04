/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturmMathlib
import HexSturmMathlib.RealClosed

namespace HexSturmMathlib.Tests.Reduced
open Hex

/-- Ordinary umbrella imports expose reduced-query correspondence, including
invalid domains; this example uses the identity real-closed interpretation. -/
theorem query_eq (p q : DensePoly ℝ) (a b : Endpoint ℝ) :
    Sturm.queryReduced Sturm.orderSign p q a b = Sturm.query Sturm.orderSign p q a b :=
  queryReduced_eq (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign orderSign_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) p q a b

theorem prepared_eq (domain : Sturm.PreparedDomain ℝ)
    (binding : domain.sign = Sturm.orderSign) (q : DensePoly ℝ) :
    Sturm.queryReducedPrepared domain q = Sturm.queryPrepared domain q :=
  queryReducedPrepared_eq (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
    Sturm.orderSign orderSign_eq (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    domain binding q

/-- info: 'HexSturmMathlib.Tests.Reduced.query_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms query_eq

/-- info: 'HexSturmMathlib.Tests.Reduced.prepared_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prepared_eq

end HexSturmMathlib.Tests.Reduced
