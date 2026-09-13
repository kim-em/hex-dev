/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Lists

public section

/-! Common-denominator encodings for rational certificate data. -/

namespace Hex.Matrix.Lists

/-- Integers representing a rational list with one positive denominator. -/
structure Scaled where
  denom : Nat
  nums : List Int
  deriving Repr, Inhabited, DecidableEq

/-- Integers representing a rational matrix with one positive denominator. -/
structure ScaledRows where
  denom : Nat
  nums : List (List Int)
  deriving Repr, Inhabited, DecidableEq

/-- Cross products identify the original rational entries without rational
arithmetic in the certificate checker. -/
@[expose] def scaleRow (d : Nat) : List Rat → List Int → Bool
  | [], [] => true
  | q :: qs, z :: zs =>
    decide (Int.mul q.num (Int.ofNat d) = Int.mul z (Int.ofNat q.den)) && scaleRow d qs zs
  | _, _ => false

/-- Check exact row lengths and entry agreement with a common denominator. -/
@[expose] def scaleRows (d : Nat) : List (List Rat) → List (List Int) → Bool
  | [], [] => true
  | q :: qs, z :: zs => scaleRow d q z && scaleRows d qs zs
  | _, _ => false

/-- Choose a common denominator once, in the compiled producer. -/
def Scaled.encode (xs : List Rat) : Scaled :=
  let d := xs.foldl (fun d q => Nat.lcm d q.den) 1
  ⟨d, xs.map (fun q => q.num * Int.ofNat (d / q.den))⟩

/-- Choose one common denominator for the entire matrix. -/
def ScaledRows.encode (xs : List (List Rat)) : ScaledRows :=
  let d := (Scaled.encode xs.flatten).denom
  ⟨d, xs.map (fun row => row.map (fun q => q.num * Int.ofNat (d / q.den)))⟩

end Hex.Matrix.Lists
