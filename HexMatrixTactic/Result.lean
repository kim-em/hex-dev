/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBareiss
public import HexRank
public import HexRowReduce
public import HexCharPoly

public section

/-!
The uniform result record returned by the proof-producing term forms `det%`,
`rank%` and `char_poly`, its compatibility projections for the
characteristic-polynomial frontend, and the transport from the replayed Bareiss
loop to the executable determinant that the `det` frontend uses.
-/

namespace Hex

universe u v

namespace MatrixTactic

/-- A computed value of `f a` together with the proof that it is `f a`.  The
term forms `det% A`, `rank% A` and `char_poly A` return this record with `f`
the requested operation and `a` the original matrix. -/
structure Certified {α : Sort u} {β : Sort v} (f : α → β) (a : α) where
  /-- The computed value. -/
  value : β
  /-- The requested operation on the original input equals the value. -/
  proof : f a = value

namespace Certified

variable {α : Sort u} {β : Sort v} {f : α → β} {a : α}

/-- Compatibility projection for `char_poly`: the computed polynomial. -/
abbrev poly (r : Certified f a) : β := r.value

/-- Compatibility projection for `char_poly`: the characteristic-polynomial
equality. -/
theorem charPoly_eq (r : Certified f a) : f a = r.poly := r.proof

end Certified

end MatrixTactic

namespace Matrix

variable {R : Type u} [Zero R] [One R] [Neg R] [Sub R] [Mul R] [DecidableEq R] {n : Nat}

/-- A replayed Bareiss value is the executable determinant: the form the `det`
frontend emits after a kernel `decide` on `bareissReplay`. -/
theorem bareissWith_eq_of_replay (quot : R → R → R) (M : Matrix R n n) (d : R)
    (h : bareissReplay quot M = d) : bareissWith quot M = d :=
  (bareissWith_eq_replay quot M).trans h

end Matrix

end Hex
