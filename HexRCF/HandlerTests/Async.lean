/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.HandlerTests.Support

public section

namespace Hex.RCF.HandlerTests

-- This fresh module uses no observational assertions on the shared IO refs.
-- Successful auxiliary declarations and their axiom walk must also work with
-- asynchronously scheduled elaboration/kernel checking, as in Lake builds.
set_option Elab.async true

theorem asyncIdentity : ∀ x : ℝ, x + Real.pi = x + Real.pi := by rcf

/-- info: 'Hex.RCF.HandlerTests.asyncIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asyncIdentity

end Hex.RCF.HandlerTests
