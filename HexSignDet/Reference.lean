/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Produce

public section

/-! Exponential full-ternary reference construction for small-case comparisons.
Production recursion never calls this module. -/
namespace Hex.SignDet

/-- Ordered words, with the first coordinate varying slowest. -/
@[expose] def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (words alphabet n).map (a :: ·)

/-- The full tensor moment system. This deliberately performs `3^s` queries;
it is a reference for conformance and performance comparisons, not a fallback. -/
@[expose] def referencePrepared {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
    [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
    (context : Ctx) (domain : Sturm.PreparedDomain E) (qs : List (DensePoly E)) :
    Except BuildError (Node E Ctx) :=
  buildNode context domain qs (words [0, 1, 2] qs.length) (words [-1, 0, 1] qs.length)

end Hex.SignDet
