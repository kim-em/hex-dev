/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib
import HexECPPMathlib.Native
import HexECPPMathlib.Pari
import Batteries.Tactic.Lint
import Mathlib.Tactic.Linter.Lint

/-! # Companion API lint regression

Legacy import syntax retains imported docstring metadata for the linter. Run
the default Mathlib/Batteries lint set and theorem documentation coverage on
the companion's module prefix, including the optional elaborators and IO API.
-/

#lint- docBlameThm in HexECPPMathlib
