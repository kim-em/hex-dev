/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexOrderedFnMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Ordered-function API lint checks

Legacy imports retain imported docstring metadata for the environment linters.
The checks select the computational and semantic modules by their module roots,
and include theorem documentation.
-/

open Batteries.Tactic.Lint in
/-- The theorem documentation check excludes the `@[ext]`-generated iff lemma,
which is unavailable for a source docstring in the computational module. -/
@[env_linter disabled] def docBlameThm' : Linter :=
  { docBlameThm with
    test := fun declName => do
      if declName == `Hex.OrderedFn.Real.Extension.ext_iff then return none
      docBlameThm.test declName }

#lint- docBlame docBlameThm' in HexOrderedFn

#lint- docBlame docBlameThm' in HexOrderedFnMathlib
