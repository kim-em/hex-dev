/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSturmMathlib
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint

/-! Environment lints cover both production module roots, including theorem
documentation. Legacy imports retain the imported docstring metadata needed by
these checks. Individual proof/API and use assessment remain separate requirements.
The computational Sturm regression belongs to HexSturm; this correspondence
companion has no compiled benchmark track. -/

#lint- docBlame docBlameThm in HexSturm
#lint- docBlame docBlameThm in HexSturmMathlib
