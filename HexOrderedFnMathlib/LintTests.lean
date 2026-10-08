/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnMathlib
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint
public import Mathlib.Tactic.Linter.Style
public import Mathlib.Tactic.Linter.TacticDocumentation

public section

/-!
# Ordered-function API lint checks

Legacy imports retain imported docstring metadata for the environment linters.
The checks select the computational and semantic modules by their module roots,
and include theorem documentation.
-/

#lint- docBlame docBlameThm in HexOrderedFn

#lint- docBlame docBlameThm in HexOrderedFnMathlib
