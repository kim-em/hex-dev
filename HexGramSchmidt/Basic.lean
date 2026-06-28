/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Basic.Kernel
public import HexGramSchmidt.Basic.Linearity
public import HexGramSchmidt.Basic.Rat
public import HexGramSchmidt.Basic.IntCast

public section

/-!
Integer Gram-Schmidt core for `hex-gram-schmidt`: the executable/noncomputable
basis and coefficient construction, its linearity and span/orthogonality
support, the rational-valued API, and the integer-cast layer. Split by subject
across `HexGramSchmidt/Basic/*`; this module re-exports them.
-/
