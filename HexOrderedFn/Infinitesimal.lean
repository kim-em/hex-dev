/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRationalFn

@[expose] public section

/-! Positive infinitesimal orders on canonical rational functions.
Use `open scoped Hex.OrderedFn.Infinitesimal` for comparisons. The explicit
sign and comparison functions also accept a predecessor sign directly. -/

namespace Hex.OrderedFn

/-- The executable sign of an ordered coefficient. -/
def orderSign {K : Type u} [Zero K] [LT K] [DecidableLT K] [DecidableEq K]
    (a : K) : Int :=
  if a < 0 then -1 else if a = 0 then 0 else 1

namespace Infinitesimal

variable {K : Type u}

/-- Scan from degree zero, returning the array size when all coefficients vanish. -/
def lowestIndex [Zero K] [DecidableEq K] (p : DensePoly K) : Nat :=
  p.coeffs.findIdx (fun c => c != 0)

/-- The first nonzero coefficient, or zero for the zero polynomial. -/
def lowestCoeff [Zero K] [DecidableEq K] (p : DensePoly K) : K :=
  p.coeff (lowestIndex p)

/-- Sign at a positive infinitesimal, using the predecessor field's total sign.
Both coefficients matter: a monic denominator can have a negative lowest coefficient. -/
def sign [Lean.Grind.Field K] [DecidableEq K] (baseSign : K → Int)
    (f : RationalFn K) : Int :=
  baseSign (lowestCoeff f.num) * baseSign (lowestCoeff f.den)

/-- Compare canonical fractions by the sign of their difference. -/
def compare [Lean.Grind.Field K] [DecidableEq K] (baseSign : K → Int)
    (f g : RationalFn K) : Ordering :=
  let s := sign baseSign (f - g)
  if s < 0 then .lt else if s = 0 then .eq else .gt

/-- Nonstrict order at a positive infinitesimal. -/
scoped instance [Lean.Grind.Field K] [DecidableEq K] [LT K] [DecidableLT K] :
    LE (RationalFn K) := ⟨fun f g => sign orderSign (f - g) ≤ 0⟩

scoped instance [Lean.Grind.Field K] [DecidableEq K] [LT K] [DecidableLT K] :
    LT (RationalFn K) := ⟨fun f g => sign orderSign (f - g) < 0⟩

scoped instance [Lean.Grind.Field K] [DecidableEq K] [LT K] [DecidableLT K] :
    DecidableLE (RationalFn K) := fun _ _ => inferInstanceAs (Decidable (_ ≤ (0 : Int)))

scoped instance [Lean.Grind.Field K] [DecidableEq K] [LT K] [DecidableLT K] :
    DecidableLT (RationalFn K) := fun _ _ => inferInstanceAs (Decidable (_ < (0 : Int)))

end Infinitesimal
end Hex.OrderedFn
