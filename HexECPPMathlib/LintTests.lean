/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexECPPMathlib
public import HexECPPMathlib.Native
public import HexECPPMathlib.Pari
public import Batteries.Tactic.Lint
public import Mathlib.Tactic.Linter.Lint

import all HexECPPMathlib.Compact
import all HexECPPMathlib.Elab
import all HexECPPMathlib.Hasse
import all HexECPPMathlib.Hasse.Degree
import all HexECPPMathlib.Hasse.Frobenius
import all HexECPPMathlib.Native
import all HexECPPMathlib.Order
import all HexECPPMathlib.Pari
import all HexECPPMathlib.Pari.IO
import all HexECPPMathlib.Pari.Process
import all HexECPPMathlib.Policy
import all HexECPPMathlib.Reduction
import all HexECPPMathlib.Soundness

import all HexPrimality.Elab

section

/-! # Companion API lint regression

Private module imports retain imported docstrings and declaration bodies. Run
the default Mathlib/Batteries lint set and theorem documentation coverage on
the companion's module prefix, including the optional elaborators and IO API.
-/

#lint- docBlameThm in HexECPPMathlib
