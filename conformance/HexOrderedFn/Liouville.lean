/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnMathlib.LiouvilleTests
public meta import HexOrderedFnMathlib.LiouvilleTests
public meta import HexOrderedFn.Real
public meta import HexOrderedFn.Extension
public meta import HexOrderedFn.ExtensionTests

open Hex.OrderedFn Hex.OrderedFn.Real Hex.OrderedFn.LiouvilleTests

local instance (priority := 2000) : Lean.Grind.Field Rat := Field.toGrindField

-- Execute the core algorithms with the companion's proved caller oracle.
#guard attempt source positive.val 2 == some 1
#guard attempt source negative.val 0 == some (-1)
#guard attempt source quotient.val 2 == some (-1)
#guard Extension.sign positive == 1
#guard Extension.sign negative == -1
#guard Extension.sign quotient == -1
#guard Extension.sign (ExtensionTests.zero registered) == 0
#guard (Extension.approx positive (1 / 8)).width ≤ 1 / 8
#guard Extension.sign (Extension.transport refined positive) == 1
#guard ExtensionTests.epsilonSign registered == 1
