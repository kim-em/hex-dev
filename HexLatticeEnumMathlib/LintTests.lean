/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLatticeEnumMathlib
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Linter.TacticDocumentation

import all HexLatticeEnum.Basic
import all HexLatticeEnum.Bounds
import all HexLatticeEnum.Cert
import all HexLatticeEnum.Closest
import all HexLatticeEnum.Decode
import all HexLatticeEnum.Enumerate
import all HexLatticeEnum.GramSchmidt
import all HexLatticeEnum.Preprocess
import all HexLatticeEnum.Shortest
import all HexLatticeEnumMathlib.Bounds
import all HexLatticeEnumMathlib.Budget
import all HexLatticeEnumMathlib.Cert
import all HexLatticeEnumMathlib.Closest
import all HexLatticeEnumMathlib.Correspondence
import all HexLatticeEnumMathlib.Distance
import all HexLatticeEnumMathlib.Enumerate
import all HexLatticeEnumMathlib.Geometry
import all HexLatticeEnumMathlib.GramSchmidt
import all HexLatticeEnumMathlib.Native
import all HexLatticeEnumMathlib.OptimizationBudget
import all HexLatticeEnumMathlib.Order
import all HexLatticeEnumMathlib.Preprocess
import all HexLatticeEnumMathlib.Shortest
import all HexLatticeEnumMathlib.TransportCert
import all HexLatticeEnumMathlib.Traversal

public section

/-!
# Lattice-enumeration lint regression

The explicit `import all` declarations retain docstrings and private proof
helpers for linting. Ordinary module imports omit that metadata.

The run covers the Mathlib-free implementation and its Mathlib companion. Batteries' default linter set includes `docBlame`; the local
theorem linter below makes theorem docstring coverage build-enforced too.
-/

open Batteries.Tactic.Lint in
/-- `docBlameThm`, excluding compiler-generated enum constructor-index
theorems that cannot carry a source docstring. -/
@[env_linter disabled] meta def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName.components.getLast? == some `ofNat_ctorIdx then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in Hex.LatticeEnum

#lint- docBlame docBlameThm' in HexLatticeEnumMathlib
