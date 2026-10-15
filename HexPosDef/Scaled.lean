/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDef.Certificate
public import HexMatrix.Scaled

public section

/-! One common positive denominator for rational complex components. -/

namespace Hex.PosDef.Gaussian

/-- Both components of every entry share the same denominator. -/
structure ScaledRows where
  denom : Nat
  nums : List (List Gaussian)
  deriving Repr, Inhabited, DecidableEq

/-- Cross-multiplication identifies both components without rational dot products. -/
@[expose] def scaleRow (s : Nat) : List (Rat × Rat) → List Gaussian → Bool
  | [], [] => true
  | (re, im) :: xs, z :: zs =>
      decide (Int.mul re.num (Int.ofNat s) = Int.mul z.re (Int.ofNat re.den)) &&
      decide (Int.mul im.num (Int.ofNat s) = Int.mul z.im (Int.ofNat im.den)) &&
      scaleRow s xs zs
  | _, _ => false

@[expose] def scaleRows (s : Nat) : List (List (Rat × Rat)) → List (List Gaussian) → Bool
  | [], [] => true
  | row :: rows, z :: zs => scaleRow s row z && scaleRows s rows zs
  | _, _ => false

/-- Choose one scale for real and imaginary components throughout the matrix. -/
def ScaledRows.encode (rows : List (List (Rat × Rat))) : ScaledRows :=
  let components := rows.flatten.flatMap (fun (re, im) => [re, im])
  let s := (Hex.Matrix.Lists.Scaled.encode components).denom
  ⟨s, rows.map (fun row => row.map (fun (re, im) =>
    ⟨re.num * Int.ofNat (s / re.den), im.num * Int.ofNat (s / im.den)⟩))⟩

end Hex.PosDef.Gaussian
