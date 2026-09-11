/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetMathlib.Basic
public import HexDetMathlib.Small
public import HexDetMathlib.Bareiss
public import HexDetMathlib.Berkowitz
public import HexDetMathlib.Field
public import HexDetMathlib.Integer
public import HexDetMathlib.Carriers

public section

/-!
The `HexDetMathlib` library is the correctness companion for `HexDet`. It owns
no runtime determinant, conformance driver, benchmark or tactic: `HexDet` is the
computational conformance and performance owner.

Every shipped arm is proved equal to the Leibniz reference determinant
`Hex.Matrix.det` by composing the algorithm correspondences of
`HexBareissMathlib` and `HexCharPolyMathlib`, and dispatch is proved to report
only routes it is entitled to report. Both sides of the first law are
Mathlib-free expressions, but the proof is not: a Mathlib-free proof of the
Berkowitz determinant identity is future work.
-/
