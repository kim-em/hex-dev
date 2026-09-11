/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Reduce

public section

/-!
Entry points of the rank producer.

`rankCertWith` runs `rowReduceWith` on `A` to obtain the pivot rows and
columns, forms `[B | 1]` for the pivot block `B`, runs `rowReduceWith` on it,
and reads the adjugate of `B` off the right block of the pivot rows of that
second pass, with its `denom`. `rankWith` and `rankProfileWith` are unchecked
and fast; `certifyRankWith` returns the certificate together with its check.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} {n m : Nat}

/-- The rank profile: pivot rows in elimination order, pivot columns
increasing. Unchecked; its correctness is the companion's
`rankCertWith_check` with soundness. -/
@[expose]
def rankProfileWith [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : RankProfile n m :=
  (rowReduceWith quot A).profile

/-- The block `[B | 1]` on which the second pass of `rankCertWith` runs. -/
@[expose]
def augmentIdentity [Zero R] [One R] {r : Nat} (B : Matrix R r r) : Matrix R r (r + r) :=
  ofFn fun i j =>
    if h : j.val < r then B[(i, (⟨j.val, h⟩ : Fin r))]
    else if i.val + r = j.val then 1 else 0

/-- The row of a second-pass reduced form that carries the `k`-th pivot. The
second pass over `[B | 1]` finds every row of `B` a pivot row (the companion's
`rankCertWith_check` proves the pass has full rank), so the index is always in
range and the default is never read. -/
@[expose]
def pivotRowAt {r : Nat} (D : ReducedForm R r (r + r)) (k : Fin r) : Fin r :=
  D.profile.rows.toArray.getD k.val k

/-- The adjugate of the pivot block, read off the right block of the pivot
rows of a pass over `[B | 1]`, in elimination order. -/
@[expose]
def adjugateOf {r : Nat} (D : ReducedForm R r (r + r)) : Matrix R r r :=
  ofFn fun k l => D.matrix[(pivotRowAt D k, (⟨r + l.val, by omega⟩ : Fin (r + r)))]

/-- The certificate assembled from a first pass `D` over `A`: the profile of
`D`, and the adjugate of the pivot block with its determinant from one pass
over `[B | 1]`. -/
@[expose]
def rankCertOf [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) (D : ReducedForm R n m) : RankCert R n m :=
  let D₂ := rowReduceWith quot (augmentIdentity (selectedSubmatrix A D.profile.rows D.profile.cols))
  { rank := D.profile.rank
    rows := D.profile.rows
    cols := D.profile.cols
    denom := D₂.denom
    adj := adjugateOf D₂ }

/-- The certificate: the profile of one pass over `A`, and the adjugate of the
pivot block with its determinant from one pass over `[B | 1]`. -/
@[expose]
def rankCertWith [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : RankCert R n m :=
  rankCertOf quot A (rowReduceWith quot A)

/-- The certificate, checked. Under the producer contract (`quot` is an exact
quotient, `quot (a * b) b = a` for `b ≠ 0`, over a nontrivial ring) the `none`
branch is unreachable: the companion's `rankCertWith_check` proves every
produced certificate checks. With a quotient that violates the contract the
certificate can fail the check and `none` is returned. -/
@[expose]
def certifyRankWith [Lean.Grind.CommRing R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : Option (RankCert R n m) :=
  let c := rankCertWith quot A
  if checkRank A c then some c else none

/-- The rank. Unchecked and fast. -/
@[expose]
def rankWith [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : Nat :=
  (rankProfileWith quot A).rank

/-- The certificate's index sets are the profile of the first pass. -/
theorem rankCertWith_rank [Zero R] [One R] [Sub R] [Mul R] [DecidableEq R] (quot : R → R → R)
    (A : Matrix R n m) : (rankCertWith quot A).rank = rankWith quot A := rfl

end Hex.Matrix
