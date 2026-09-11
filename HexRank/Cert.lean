/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminant

public section

/-!
The two-sided rank certificate and its checker.

A `RankCert` names an `r × r` submatrix `B` of `A` at `rows × cols` and
carries a matrix `adj` and a scalar `denom` with `B * adj = denom • 1`. The
checker `checkRank` verifies that identity, that `denom ≠ 0`, and that
`denom • A = A[·, cols] * (adj * A[rows, ·])`, using ring arithmetic and
equality tests only. The producer fills `adj` and `denom` with `adjugate B`
and `det B`; the checker requires only the identities, and a passing check
does not establish that the fields are those values.
-/

namespace Hex.Matrix

open scoped Hex

universe u

variable {R : Type u} {n m : Nat}

/-- A two-sided rank certificate: a `rank × rank` submatrix `B` of `A` at
`rows × cols`, and a matrix `adj` and scalar `denom ≠ 0` with
`B * adj = denom • 1`. The producer fills them with `adjugate B` and
`det B`; the checker requires only the identity. The index vectors are
selections, not sets: the checker imposes no ordering or distinctness
condition on them, and a repeated index fails the nonsingularity test. -/
structure RankCert (R : Type u) (n m : Nat) where
  /-- The certified rank. -/
  rank : Nat
  /-- Row indices of the nonsingular block, in any order. -/
  rows : Vector (Fin n) rank
  /-- Column indices of the nonsingular block, in any order. -/
  cols : Vector (Fin m) rank
  /-- The nonzero denominator of `B⁻¹`; `det B` for the producer. -/
  denom : R
  /-- The numerator of `B⁻¹`; `adjugate B` for the producer. -/
  adj : Matrix R rank rank

/-- The scalar multiple `c • M` in `ofFn` form. The `SMul` instance on
matrices maps over the buffer through core's `Vector.map`, whose body is not
exposed across a module boundary, so a `decide +kernel` through it sticks in
any importing `module` file; this form reduces. -/
@[expose]
def scale [Mul R] (c : R) (M : Matrix R n m) : Matrix R n m :=
  ofFn fun i j => c * M[(i, j)]

/-- `scale` is the scalar multiple. -/
theorem scale_eq_smul [Mul R] (c : R) (M : Matrix R n m) : scale c M = c • M := by
  apply ext_getElem
  intro i j
  rw [scale, getElem_ofFn, getElem_pair_eq_nested, smul_getElem]
  rfl

/-- Check a rank certificate. Ring arithmetic and equality tests only: no
division, no determinant, no search. Kernel-reducible on closed inputs. -/
@[expose]
def checkRank [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix R n m) (c : RankCert R n m) : Bool :=
  let B := selectedSubmatrix A c.rows c.cols
  let C := selectCols A c.cols
  let P := selectRows A c.rows
  decide (c.denom ≠ 0) &&
  decide (B * c.adj = scale c.denom (Matrix.identity c.rank)) &&
  decide (scale c.denom A = C * (c.adj * P))

/-- A certificate checks exactly when its three identities hold. -/
theorem checkRank_iff [Lean.Grind.CommRing R] [DecidableEq R]
    (A : Matrix R n m) (c : RankCert R n m) :
    checkRank A c = true ↔
      c.denom ≠ 0 ∧
      selectedSubmatrix A c.rows c.cols * c.adj = c.denom • Matrix.identity c.rank ∧
      c.denom • A = selectCols A c.cols * (c.adj * selectRows A c.rows) := by
  simp [checkRank, and_assoc, scale_eq_smul]

end Hex.Matrix
