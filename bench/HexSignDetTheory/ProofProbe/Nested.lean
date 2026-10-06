/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Nested.N1.Accept
public import HexSignDetTheory.Diagnostics.Nested.N1.RejectArithmetic
public import HexSignDetTheory.Diagnostics.Nested.N1.ArithmeticCause
public import HexSignDetTheory.Diagnostics.Nested.N1.AcceptFraction
public import HexSignDetTheory.Diagnostics.Nested.N1.RejectStale
public import HexSignDetTheory.Diagnostics.Nested.N1.RejectProduct
public import HexSignDetTheory.Diagnostics.Nested.N1.Certificates

/-! Nested coefficient acceptance and rejection examples. Imported examples use the ordinary
Lean kernel and guard their theorem axiom inventories. -/

public section

namespace Hex.SignDetMathlib.ProofProbe
open Hex.SignDetMathlib.Diagnostics

/-- Re-export ordinary-kernel acceptance of the exact nested literal evidence
from the warm diagnostic dependency. -/
theorem nested_accept : Nested.check 1 = true := Nested.N1.Accept.checked

/-- A copied child binding cannot prove the requested nested result. -/
theorem nested_stale : Nested.check 1 true = false := Nested.N1.RejectStale.checked

/-- False coefficient arithmetic is rejected even with the right binding. -/
theorem nested_arithmetic : Nested.check 1 false true = false :=
  Nested.N1.RejectArithmetic.checked

/-- info: 'Hex.SignDetMathlib.ProofProbe.nested_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_accept

/-- info: 'Hex.SignDetMathlib.ProofProbe.nested_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_stale

/-- info: 'Hex.SignDetMathlib.ProofProbe.nested_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_arithmetic

end Hex.SignDetMathlib.ProofProbe
