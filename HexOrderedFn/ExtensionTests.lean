/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Extension
public import HexOrderedFn.Infinitesimal

/-!
Core arithmetic queries shared by semantic proofs and compiled real-extension tests.
-/

@[expose] public section

namespace Hex.OrderedFn.Real.ExtensionTests

variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K] (r : Registration K)

def positive : Extension r := Extension.X - Extension.C (5 / 4 : K)
def negative : Extension r := Extension.X - Extension.C (2 : K)
def quotient : Extension r := positive r / negative r
def zero : Extension r := Extension.X - Extension.X

abbrev Mixed := RationalFn (Extension r)
def epsilon : Mixed r := RationalFn.X
def epsilonSign : Int := Infinitesimal.sign Extension.sign (epsilon r)

end Hex.OrderedFn.Real.ExtensionTests
