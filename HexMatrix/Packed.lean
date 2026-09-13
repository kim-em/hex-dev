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

Everything here is structural recursion over lists and `Nat` primitives;
the soundness lemmas are in `HexMatrixMathlib.Packed`.
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

end Hex.Matrix.Packed
