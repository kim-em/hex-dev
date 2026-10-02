/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss.Kernel

@[expose] public section

namespace Hex.Matrix

/-- Operations on the serialized entries of a determinant certificate.
The companion supplies canonical polynomial lists and their denotation laws. -/
structure DetOps (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  beq : R → R → Bool
  valid : R → Bool

namespace DetOps

variable (ops : DetOps R)

/-- A row entry, with zero beyond the end. -/
def entry : List R → Nat → R
  | [], _ => ops.zero
  | x :: _, 0 => x
  | _ :: xs, n + 1 => entry xs n

/-- Dot product, stopping at the shorter list. -/
def dot : List R → List R → R
  | x :: xs, y :: ys => ops.add (ops.mul x y) (dot xs ys)
  | _, _ => ops.zero

/-- Column extraction uses only structural list recursion. -/
def column (j : Nat) : List (List R) → List R
  | [] => []
  | r :: rs => ops.entry r j :: column j rs

/-- Consecutive columns, starting at the supplied index. -/
def columns (A : List (List R)) (start : Nat) : Nat → List (List R)
  | 0 => []
  | n + 1 => ops.column start A :: columns A (start + 1) n

/-- Canonicality of every entry in a row. -/
def validRow : List R → Bool
  | [] => true
  | x :: xs => ops.valid x && validRow xs

/-- Canonicality of every entry in every row. -/
def validRows : List (List R) → Bool
  | [] => true
  | r :: rs => ops.validRow r && validRows rs

/-- Orthogonality against each supplied column. -/
def zeroDots (v : List R) : List (List R) → Bool
  | [] => true
  | c :: cs => ops.beq (ops.dot v c) ops.zero && zeroDots v cs

/-- At least one entry is nonzero. -/
def anyNonzero : List R → Bool
  | [] => false
  | x :: xs => !(ops.beq x ops.zero) || anyNonzero xs

/-- Apply the sign of the row permutation without a coefficient cast. -/
def signed : List (Nat × Nat) → R → R
  | [], x => x
  | _ :: swaps, x => ops.neg (signed swaps x)

/-- Check the transform and adjacent diagonals. The last computed diagonal
is retained instead of multiplying all pivot polynomials. -/
def triangular (d : R) (swaps : List (Nat × Nat)) :
    List (List R) → Nat → List (List R) → List (List R) → R → Bool
  | _, _, [], [], prev => ops.beq d (ops.signed swaps prev)
  | done, i, t :: ts, c :: cs, prev =>
      let l := ops.entry t i
      Nat.beq t.length (i + 1) && ops.validRow t &&
        !(ops.beq l ops.zero) && ops.beq l prev && ops.zeroDots t done &&
        triangular d swaps (c :: done) (i + 1) ts cs (ops.dot t c)
  | _, _, _, _, _ => false

end DetOps

namespace DetWitness

/-- Map all entries of a witness, for conversion from executable entries to
their serialized representation. -/
def map (f : R → S) : DetWitness R → DetWitness S
  | .triangular s t d => .triangular s (t.map (List.map f)) (f d)
  | .singular v => .singular (v.map f)

/-- A row of a serialized matrix, with the empty row beyond its end. -/
def row : List (List R) → Nat → List R
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, i + 1 => row rs i

/-- Replace a row, leaving out-of-range indices unchanged. -/
def replace : List (List R) → Nat → List R → List (List R)
  | [], _, _ => []
  | _ :: rs, 0, r => r :: rs
  | r :: rs, i + 1, s => r :: replace rs i s

/-- Exchange two rows. Bounds and distinctness are checked separately. -/
def swap (a b : Nat) (A : List (List R)) : List (List R) :=
  replace (replace A a (row A b)) b (row A a)

/-- Apply row swaps in their recorded order. -/
def permute : List (Nat × Nat) → List (List R) → List (List R)
  | [], A => A
  | (a, b) :: ss, A => permute ss (swap a b A)

/-- Verify the number of entries in every row. -/
def rowLengths (n : Nat) : List (List R) → Bool
  | [] => true
  | r :: rs => Nat.beq r.length n && rowLengths n rs

end DetWitness

/-- A determinant checker parameterized by serialized entry arithmetic.
Canonicality, shapes and swap bounds are checked before the arithmetic.
For nonempty triangular witnesses, the diagonal walk requires the first
transform diagonal to be one and each later one to equal the preceding
product diagonal. The empty case requires the value one. -/
def checkDetPolyList (ops : DetOps R) (n : Nat) (A : List (List R)) :
    DetWitness R → Bool
  | .triangular swaps T d =>
      Nat.beq A.length n && DetWitness.rowLengths n A && ops.validRows A &&
        DetWitness.swapsOk n swaps && ops.valid d &&
        ops.triangular d swaps [] 0 T
          (ops.columns (DetWitness.permute swaps A) 0 n) ops.one
  | .singular v =>
      Nat.beq A.length n && DetWitness.rowLengths n A && ops.validRows A &&
        Nat.beq v.length n && ops.validRow v && ops.anyNonzero v &&
        ops.zeroDots v (ops.columns A 0 n)

end Hex.Matrix
