/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPoly.Kernel
public import HexMatrix.Packed

@[expose] public section

/-!
Integer expression trees and bounded arithmetic for Kronecker substitution.
The checker retains the input tree; these operations never normalize it.
-/

namespace Hex.Kronecker

/-- The fixed commutative-ring language, independent of the reifier. -/
inductive Expr where
  | int (z : Int)
  | atom (i : Nat)
  | add (a b : Expr)
  | sub (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (n : Nat)
  deriving Repr, DecidableEq

/-- Limits on dense digits and on the bits of packed operands and intermediates. -/
structure Budget where
  maxDenseDigits : Nat := 65536
  maxPackedBits : Nat := 16777216
  deriving Repr, BEq, Inhabited

namespace Saturating

/-- Addition capped before constructing an oversized sum. -/
def add (cap a b : Nat) : Nat :=
  if cap ≤ a then cap else if cap - a ≤ b then cap else a + b

/-- Multiplication capped before constructing an oversized product. -/
def mul (cap a b : Nat) : Nat :=
  if a == 0 || b == 0 then 0
  else if cap ≤ a then cap
  else if (cap - 1) / a < b then cap else a * b

/-- Square-and-multiply, structurally recursive in fuel. The public caller
supplies the exponent as fuel; halving the exponent uses at most that many steps. -/
def powAux (cap : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => min 1 cap
  | fuel + 1, a, n =>
      if n == 0 then min 1 cap
      else if a == 0 then 0
      else
        let q := powAux cap fuel a (n / 2)
        if cap ≤ q then cap
        else
          let square := mul cap q q
          if n % 2 == 0 then square else mul cap square a

/-- Exact power below the cap, and the cap otherwise; in particular `a^0 = 1`. -/
def pow (cap a n : Nat) : Nat := powAux cap n a n

end Saturating

/-- A degree vector of the declared arity. -/
def zeroDegrees : Nat → List Nat
  | 0 => []
  | k + 1 => 0 :: zeroDegrees k

/-- The degree vector of an atom. Index validity is checked separately. -/
def atomDegrees : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, 0 => 1 :: zeroDegrees k
  | k + 1, i + 1 => 0 :: atomDegrees k i

/-- Componentwise maximum. All checker inputs have the same validated arity. -/
def maxDegrees : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => max a b :: maxDegrees as bs

/-- Componentwise sum. -/
def addDegrees : List Nat → List Nat → List Nat
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addDegrees as bs

/-- Multiplying a degree vector by a literal exponent. -/
def scaleDegrees (n : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => (n * d) :: scaleDegrees n ds

namespace Expr

/-- Reject every out-of-range atom, including atoms below a zero power. -/
@[reducible] def wellFormed (k : Nat) : Expr → Bool
  | .int _ => true
  | .atom i => i < k
  | .add a b | .sub a b | .mul a b => wellFormed k a && wellFormed k b
  | .neg a | .pow a _ => wellFormed k a

/-- Every occurring atom belongs to the declared arity. -/
abbrev WellFormed (e : Expr) (k : Nat) : Prop := wellFormed k e = true

/-- Structural per-atom degree bounds, without using cancellation. -/
def degrees (k : Nat) : Expr → List Nat
  | .int _ => zeroDegrees k
  | .atom i => atomDegrees k i
  | .add a b | .sub a b => maxDegrees (degrees k a) (degrees k b)
  | .neg a => degrees k a
  | .mul a b => addDegrees (degrees k a) (degrees k b)
  | .pow a n => scaleDegrees n (degrees k a)

/-- Structural coefficient ℓ¹ bound. The preflight uses the capped version. -/
def height : Expr → Nat
  | .int z => z.natAbs
  | .atom _ => 1
  | .add a b | .sub a b => height a + height b
  | .neg a => height a
  | .mul a b => height a * height b
  | .pow a n => height a ^ n

/-- Structural coefficient bound computed exactly up to the supplied cap. -/
def cappedHeight (cap : Nat) : Expr → Nat
  | .int z => min z.natAbs cap
  | .atom _ => min 1 cap
  | .add a b | .sub a b => Saturating.add cap (cappedHeight cap a) (cappedHeight cap b)
  | .neg a => cappedHeight cap a
  | .mul a b => Saturating.mul cap (cappedHeight cap a) (cappedHeight cap b)
  | .pow a n => Saturating.pow cap (cappedHeight cap a) n

/-- Integer literals in a residue-provider tree must be canonical representatives. -/
def residues (p : Nat) : Expr → Bool
  | .int z => 0 ≤ z && z < (p : Int)
  | .atom _ => true
  | .add a b | .sub a b | .mul a b => residues p a && residues p b
  | .neg a | .pow a _ => residues p a

end Expr

/-- Integer square-and-multiply. No intermediate power exceeds the exponent. -/
def powAux : Nat → Int → Nat → Int
  | 0, _, _ => 1
  | fuel + 1, a, n =>
      if n == 0 then 1 else
        let q := powAux fuel a (n / 2)
        let square := q * q
        if n % 2 == 0 then square else square * a

/-- A literal integer power, with a structural fuel argument hidden from callers. -/
def power (a : Int) (n : Nat) : Int := powAux n a n

/-- Mixed-radix code of an exponent list. Validated plans ensure equal lengths. -/
def code : List Nat → List Nat → Nat
  | s :: ss, e :: es => e * s + code ss es
  | _, _ => 0

/-- Evaluate the original tree at the Kronecker substitution. -/
def evalKron (base : Nat) (strides : List Nat) : Expr → Int
  | .int z => z
  | .atom i => power (Int.ofNat base) (strides.getD i 0)
  | .add a b => evalKron base strides a + evalKron base strides b
  | .sub a b => evalKron base strides a - evalKron base strides b
  | .neg a => -evalKron base strides a
  | .mul a b => evalKron base strides a * evalKron base strides b
  | .pow a n => power (evalKron base strides a) n

/-- Pack a supplied support directly, without filling the dense box. The public
checks validate exponent lists before calling this evaluator. -/
def packTerms (base : Nat) (strides : List Nat) : Hex.MvPoly.Kernel.PolyList Int → Int
  | [] => 0
  | (e, c) :: ts => c * power (Int.ofNat base) (code strides e) + packTerms base strides ts

end Hex.Kronecker
