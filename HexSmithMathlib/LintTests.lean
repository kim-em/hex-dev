/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmithMathlib
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Linter.TacticDocumentation

import all HexSmith.Cert
import all HexSmith.Contracts
import all HexSmith.Correct.Complete
import all HexSmith.Correct.Core
import all HexSmith.Correct
import all HexSmith.Diagonal
import all HexSmith.Divisor
import all HexSmith.Kernel
import all HexSmith.Smith
import all HexSmith.Structure
import all HexSmith.Unique
import all HexSmithMathlib.Basis
import all HexSmithMathlib.Chain
import all HexSmithMathlib.Kernel
import all HexSmithMathlib.Quotient
import all HexSmithMathlib.Rank
import all HexSmithMathlib.Tactic

public section

/-!
# Integer Smith-normal-form lint regression

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

#lint- docBlame docBlameThm' in HexSmith

#lint- docBlame docBlameThm' in HexSmithMathlib
