/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Kronecker-packed dot products for kernel certificate checkers.

A row of natural numbers `a₀, …, a_{r−1}` packs into the one number
`Σ aₖ · 2^(W·k)` (`packRow`), and a column into the same shape in reverse
order, cut or zero-padded to `r` entries (`packCol`).  The product of a
packed row and a reverse-packed column is the digit list, in base `2^W`,
of the convolution of the two rows, and its slot `r − 1` is their dot
product (`dotPacked`), as long as no convolution coefficient reaches
`2^W`: a checker using these must bound the entries so that
`r · bound² < 2^W`.  In the kernel a dot product is then one GMP
multiplication, one shift and one mask (`Nat.mul`, `Nat.shiftRight`,
`Nat.land`, all accelerated) in place of `r` multiply-adds.

A signed row is packed as the pair of its nonnegative and negated
nonpositive parts (`packSignedCut`, `packSignedCol`), and the signed dot
product is the four packed products combined (`dotIntPacked`); the bound
is then on absolute values (`allAbsLt`).  The one-pass transpose `columns`
and the plain dot products `dotNat` and `dotInt` are here as well, shared
by the rank and determinant checkers.

Everything here is structural recursion over lists and `Nat`/`Int`
primitives; the soundness lemmas are in `HexMatrixMathlib.Packed`.
-/

namespace Hex.Matrix.Packed

/-- The dot product of two natural-number lists, stopping at the shorter. -/
@[expose] def dotNat : List Nat → List Nat → Nat
  | a :: as, b :: bs => Nat.add (Nat.mul a b) (dotNat as bs)
  | _, _ => 0

/-- A row packed into one number with `W`-bit slots: `Σ aₖ · 2^(W·k)`. -/
@[expose] def packRow (W : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => Nat.add a (Nat.shiftLeft (packRow W as) W)

/-- The rows packed. -/
@[expose] def packRows (W : Nat) : List (List Nat) → List Nat
  | [] => []
  | r :: rs => packRow W r :: packRows W rs

/-- Horner accumulation of `k` more slots from the front of a list, missing
entries read as `0`: after `k` steps from `acc`, the entries consumed sit in
reverse order below `acc`. -/
@[expose] def packRevAux (W : Nat) : Nat → Nat → List Nat → Nat
  | 0, acc, _ => acc
  | k + 1, acc, [] => packRevAux W k (Nat.shiftLeft acc W) []
  | k + 1, acc, a :: as => packRevAux W k (Nat.add (Nat.shiftLeft acc W) a) as

/-- A column of `vt` cut or zero-padded to `r` entries and packed in reverse
order, in `r` steps. -/
@[expose] def packCol (W r : Nat) (c : List Nat) : Nat := packRevAux W r 0 c

/-- The columns packed. -/
@[expose] def packCols (W r : Nat) : List (List Nat) → List Nat
  | [] => []
  | c :: cs => packCol W r c :: packCols W r cs

/-- Slot `r − 1` of `p`: bits `W·(r − 1), …, W·r − 1`. -/
@[expose] def slot (W r p : Nat) : Nat :=
  Nat.land (Nat.shiftRight p (Nat.mul W (r - 1))) (Nat.sub (Nat.pow 2 W) 1)

/-- The dot product of a packed row and a reverse-packed column of `r`
entries. -/
@[expose] def dotPacked (W r pb pc : Nat) : Nat := slot W r (Nat.mul pb pc)

/-- The dot product of two integer lists, stopping at the shorter. -/
@[expose] def dotInt : List Int → List Int → Int
  | a :: as, b :: bs => Int.add (Int.mul a b) (dotInt as bs)
  | _, _ => 0

/-- Column `j` of a row list: the specification of `columns`, not on the
kernel path. -/
@[expose] def column (j : Nat) : List (List Int) → List Int
  | [] => []
  | r :: rs => r.getD j 0 :: column j rs

/-- A row prepended entrywise to a list of columns: entry `j` of the row goes
on top of column `j`; a short row contributes `0`s, and entries past the
last column are dropped. -/
@[expose] def consCols : List Int → List (List Int) → List (List Int)
  | a :: as, c :: cs => (a :: c) :: consCols as cs
  | [], c :: cs => (0 :: c) :: consCols [] cs
  | _, [] => []

/-- `m` empty columns. -/
@[expose] def emptyCols : Nat → List (List Int)
  | 0 => []
  | k + 1 => [] :: emptyCols k

/-- The `m` columns of a row list, built in one pass over the rows: `n · m`
list steps, against the `n · m` indexed reads of `O(index)` each that
`column` would cost. -/
@[expose] def columns (m : Nat) : List (List Int) → List (List Int)
  | [] => emptyCols m
  | r :: rs => consCols r (columns m rs)

/-- The nonnegative parts of a signed row. -/
@[expose] def posParts : List Int → List Nat
  | [] => []
  | a :: as => Int.toNat a :: posParts as

/-- The nonpositive parts of a signed row, negated. -/
@[expose] def negParts : List Int → List Nat
  | [] => []
  | a :: as => Int.toNat (Int.neg a) :: negParts as

/-- Every entry has absolute value below `k`. -/
@[expose] def allAbsLt (k : Nat) : List Int → Bool
  | [] => true
  | a :: as => Nat.blt (Int.natAbs a) k && allAbsLt k as

/-- Every entry of every row has absolute value below `k`. -/
@[expose] def allAbsLtRows (k : Nat) : List (List Int) → Bool
  | [] => true
  | r :: rs => allAbsLt k r && allAbsLtRows k rs

/-- A list cut or zero-padded to `r` entries and packed in order. -/
@[expose] def packCut (W r : Nat) (l : List Nat) : Nat :=
  packRow W (List.take r l ++ List.replicate (r - l.length) 0)

/-- A signed row cut or zero-padded to `r` entries, packed as its two parts. -/
@[expose] def packSignedCut (W r : Nat) (t : List Int) : Nat × Nat :=
  (packCut W r (posParts t), packCut W r (negParts t))

/-- The rows so packed. -/
@[expose] def packSignedRows (W r : Nat) : List (List Int) → List (Nat × Nat)
  | [] => []
  | t :: ts => packSignedCut W r t :: packSignedRows W r ts

/-- A signed column cut or zero-padded to `r` entries, reverse-packed as its
two parts. -/
@[expose] def packSignedCol (W r : Nat) (c : List Int) : Nat × Nat :=
  (packCol W r (posParts c), packCol W r (negParts c))

/-- The columns so packed. -/
@[expose] def packSignedCols (W r : Nat) : List (List Int) → List (Nat × Nat)
  | [] => []
  | c :: cs => packSignedCol W r c :: packSignedCols W r cs

/-- `(t⁺ − t⁻) · (c⁺ − c⁻)` from the packed parts: four packed dot products. -/
@[expose] def dotIntPacked (W r : Nat) (t c : Nat × Nat) : Int :=
  Int.sub (Int.ofNat (Nat.add (dotPacked W r t.1 c.1) (dotPacked W r t.2 c.2)))
    (Int.ofNat (Nat.add (dotPacked W r t.1 c.2) (dotPacked W r t.2 c.1)))

end Hex.Matrix.Packed
