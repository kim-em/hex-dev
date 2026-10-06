/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDetTheory.Basic
public import HexDetTheory.Small
public import HexDetTheory.Bareiss
public import HexDetTheory.Berkowitz
public import HexDetTheory.Field
public import HexDetTheory.Integer
public import HexDetTheory.Carriers

public section

/-!
The `HexDetTheory` library is the correctness companion for `HexDet`. It owns
no runtime determinant, conformance driver, benchmark or tactic: `HexDet` is the
computational conformance and performance owner.

Every shipped arm is proved equal to the Leibniz reference determinant
`Hex.Matrix.det` by composing the algorithm correspondences of
`HexBareissTheory` and `HexCharPolyTheory`, and dispatch is proved to report
only routes it is entitled to report. Both sides of the first law are
Mathlib-free expressions, but the proof is not: a Mathlib-free proof of the
Berkowitz determinant identity is future work.
-/
