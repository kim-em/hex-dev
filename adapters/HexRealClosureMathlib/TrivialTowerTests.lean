/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TrivialTower

namespace Hex.RealClosure.Trivial.Tests

variable {registry : BaseContext.Registry}
    (suffix : Tower.Suffix (Tower.Context.base (BaseContext.rational registry)))

/-- Ordinary consumers use the actual cached factory without supplying
coefficient agreement, a canonical root, or an interpretation. -/
example (p : DensePoly suffix.context.Value) :
    (Map.ofSuffix suffix).roots p = ((Map.ofSuffix suffix).polynomial p).roots :=
  Map.ofSuffix_roots suffix p

example (a b : suffix.context.Value) :
    suffix.context.equal a b = true ↔
      (Map.ofSuffix suffix).value a = (Map.ofSuffix suffix).value b :=
  (Map.ofSuffix_model suffix).equal a b

example (a b : Tower.Root suffix.context) :
    (Map.ofSuffix suffix).compareRoots a b = a.compare b :=
  (Map.ofSuffix_model suffix).compareRoots a b

example (a b : suffix.context.Value) :
    (Map.ofSuffix suffix).compare a b = suffix.context.compare a b :=
  (Map.ofSuffix_model suffix).compare a b

example (a b : suffix.context.Value) :
    (Map.ofSuffix suffix).value (a / b) =
      (Map.ofSuffix suffix).value a / (Map.ofSuffix suffix).value b :=
  (Map.ofSuffix_model suffix).value_div a b

example (a : suffix.context.Value) :
    ((Map.ofSuffix suffix).value a).sign = suffix.context.sign a :=
  (Map.ofSuffix_model suffix).sign a

example : (Map.ofSuffix suffix).value (0 : suffix.context.Value)⁻¹ = 0 := by
  rw [(Map.ofSuffix_model suffix).value_inv,
    (Map.ofSuffix_model suffix).value_zero, inv_zero]

end Hex.RealClosure.Trivial.Tests

/-- info: 'Hex.RealClosure.Trivial.Map.ofSuffix_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.ofSuffix_model

/-- info: 'Hex.RealClosure.Trivial.Map.Model.canonical?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.canonical?_isSome

/-- info: 'Hex.RealClosure.Trivial.Map.ofSuffix_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.ofSuffix_roots

/-- info: 'Hex.RealClosure.Trivial.Map.Model.value_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.value_inv

/-- info: 'Hex.RealClosure.Trivial.Map.Model.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.root

/-- info: 'Hex.RealClosure.Trivial.Map.Model.compareRoots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.compareRoots

/-- info: 'Hex.RealClosure.Trivial.Map.Model.equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.equal

/-- info: 'Hex.RealClosure.Trivial.Map.Model.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Trivial.Map.Model.sign
