/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealTheory.Tactic
public import HexDeterminantalIdealTheory.Transport
public import HexDeterminantalIdealTheory.Rank
public import HexDeterminantalIdealTheory.Locus
public import HexDeterminantalIdealTheory.Ideal

public section

/-!
The `HexDeterminantalIdealTheory` library is the theory companion of
`hex-determinantal-ideal`. It identifies the executable minors with
`Matrix.det` of a `submatrix` (`Transport`), states the rank-versus-minors
theorem for `Matrix.rank` under any ring homomorphism into a field (`Rank`),
reads the rank-drop locus of a polynomial matrix as `MvPolynomial.zeroLocus`
of the determinantal ideal (`Locus`), and proves that `Ideal.span` of the
minors is unchanged by invertible row and column operations (`Ideal`).
-/
