/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFnTheory.LiouvilleTests

/-!
Compiled semantic integration for the test-local Liouville provider. This test
executable imports the companion; computational conformance and measurements
remain Mathlib-free. No analytic provider is exported by the library umbrella.
-/

open Hex Hex.OrderedFn Hex.OrderedFn.Real Hex.OrderedFn.LiouvilleTests

local instance (priority := 2000) : Lean.Grind.Field Rat := Field.toGrindField

/-- A finite outer query uses the first real level's derived coefficient bounds.
The rational outer subject supplies no universal transcendence registration. -/
private def secondFinite : Bool :=
  let a := Extension.approximation (r := registered) (fun _ => .singleton 3)
  let f : RationalFn E := RationalFn.X - RationalFn.C positive
  match h : attempt a f 6 with
  | none => false
  | some s => s == 1 && Real.sign a f (acc_of_success _ 6 s h 0 (by decide +kernel)) == 1

def main : IO Unit := do
  let checks : Array (String × Bool) := #[
    ("positive attempt", attempt source positive.val 2 == some 1),
    ("negative attempt", attempt source negative.val 0 == some (-1)),
    ("quotient attempt", attempt source quotient.val 2 == some (-1)),
    ("positive sign", Extension.sign positive == 1),
    ("negative sign", Extension.sign negative == -1),
    ("quotient sign", Extension.sign quotient == -1),
    ("formal zero", Extension.sign (ExtensionTests.zero registered) == 0),
    ("comparison less", Extension.compare negative positive == .lt),
    ("comparison greater", Extension.compare positive negative == .gt),
    ("comparison equal", Extension.compare positive positive == .eq),
    ("strict order", decide (negative < (0 : E)) && decide ((0 : E) < positive) &&
      !decide (positive < positive)),
    ("nonstrict order", decide (negative ≤ (0 : E)) && decide (positive ≤ positive) &&
      !decide (positive ≤ (0 : E))),
    ("approximation width", decide ((Extension.approx positive (1 / 8)).width ≤ 1 / 8)),
    ("negative approximation", decide ((Extension.approx negative (1 / 8)).width ≤ 1 / 8)),
    ("quotient approximation", decide ((Extension.approx quotient (1 / 8)).width ≤ 1 / 8)),
    ("zero approximation", Extension.approx (ExtensionTests.zero registered) (1 / 8) == .singleton 0),
    ("provider transport", Extension.sign (Extension.transport refined positive) == 1),
    ("negative transport", Extension.sign (Extension.transport refined negative) == -1),
    ("zero transport", Extension.sign (Extension.transport refined (ExtensionTests.zero registered)) == 0),
    ("infinitesimal", ExtensionTests.epsilonSign registered == 1),
    ("ordered arithmetic", Extension.sign (orderedArithmetic negative) == -1),
    ("core rational dictionary", LiouvilleCoreTests.signResult == 1),
    ("successive approximation", secondFinite)]
  for (name, passed) in checks do
    unless passed do throw (IO.userError s!"Liouville integration failed: {name}")
  IO.println s!"Liouville integration: {checks.size} checks passed"
