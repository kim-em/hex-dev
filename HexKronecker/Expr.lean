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

/-- Compilable form of the primitive recursor. The equality below is a proved
compiler rewrite; kernel evaluation uses the primitive recursor directly. -/
def Expr.recImpl {motive : Expr → Sort u}
    (int : ∀ z, motive (.int z)) (atom : ∀ i, motive (.atom i))
    (add : ∀ a b, motive a → motive b → motive (.add a b))
    (sub : ∀ a b, motive a → motive b → motive (.sub a b))
    (neg : ∀ a, motive a → motive (.neg a))
    (mul : ∀ a b, motive a → motive b → motive (.mul a b))
    (pow : ∀ a n, motive a → motive (.pow a n)) : (e : Expr) → motive e
  | .int z => int z
  | .atom i => atom i
  | .add a b => add a b (recImpl int atom add sub neg mul pow a) (recImpl int atom add sub neg mul pow b)
  | .sub a b => sub a b (recImpl int atom add sub neg mul pow a) (recImpl int atom add sub neg mul pow b)
  | .neg a => neg a (recImpl int atom add sub neg mul pow a)
  | .mul a b => mul a b (recImpl int atom add sub neg mul pow a) (recImpl int atom add sub neg mul pow b)
  | .pow a n => pow a n (recImpl int atom add sub neg mul pow a)

@[csimp] theorem Expr.rec_eq_impl : @Expr.rec = @Expr.recImpl := by
  funext motive int atom add sub neg mul pow e
  induction e <;> simp_all [recImpl]

/-- Limits on dense digits and on the bits of packed operands and intermediates. -/
structure Budget where
  maxDenseDigits : Nat := 65536
  maxPackedBits : Nat := 16777216
  deriving Repr, BEq, Inhabited

namespace Saturating

/-- Addition capped before constructing an oversized sum. A bit-length test
certifies the small case, avoiding subtraction from a large cap. -/
def add (cap a b : Nat) : Nat :=
  if a < 4294967296 && b < 4294967296 && 18446744073709551616 ≤ cap then a + b
  else if cap ≤ a then cap else if cap - a ≤ b then cap else a + b

/-- Multiplication capped before constructing an oversized product. The fit test
only selects exact arithmetic; overflow still uses the exact division guard. -/
def mul (cap a b : Nat) : Nat :=
  if a < 4294967296 && b < 4294967296 && 18446744073709551616 ≤ cap then a * b
  else if a == 0 || b == 0 then 0
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
@[reducible] def wellFormed (k : Nat) (e : Expr) : Bool :=
  Expr.rec (fun _ => true) (fun i => Nat.blt i k)
    (fun _ _ a b => a && b) (fun _ _ a b => a && b)
    (fun _ a => a) (fun _ _ a b => a && b) (fun _ _ a => a) e

/-- Every occurring atom belongs to the declared arity. -/
abbrev WellFormed (e : Expr) (k : Nat) : Prop := wellFormed k e = true

/-- Structural per-atom degree bounds, without using cancellation. -/
def degrees (k : Nat) (e : Expr) : List Nat :=
  Expr.rec (fun _ => zeroDegrees k) (atomDegrees k)
    (fun _ _ a b => maxDegrees a b) (fun _ _ a b => maxDegrees a b)
    (fun _ a => a) (fun _ _ a b => addDegrees a b)
    (fun _ n a => scaleDegrees n a) e

/-- Structural coefficient ℓ¹ bound. The preflight uses the capped version. -/
def height (e : Expr) : Nat :=
  Expr.rec Int.natAbs (fun _ => 1)
    (fun _ _ a b => Nat.add a b) (fun _ _ a b => Nat.add a b)
    (fun _ a => a) (fun _ _ a b => Nat.mul a b) (fun _ n a => Nat.pow a n) e

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
      if Nat.beq n 0 then 1 else
        let q := powAux fuel a (n / 2)
        let square := q * q
        if Nat.beq (n % 2) 0 then square else Int.mul square a

/-- A literal integer power, with a structural fuel argument hidden from callers. -/
def power (a : Int) (n : Nat) : Int := powAux n a n

/-- Mixed-radix code of an exponent list. Validated plans ensure equal lengths. -/
noncomputable def code (ss : List Nat) : List Nat → Nat :=
  List.rec (fun _ => 0) (fun s _ rest es => match es with
    | [] => 0
    | e :: es => Nat.add (Nat.mul e s) (rest es)) ss

@[simp] theorem code_nil (es : List Nat) : code [] es = 0 := rfl
@[simp] theorem code_nil_right (ss : List Nat) : code ss [] = 0 := by cases ss <;> rfl
@[simp] theorem code_cons_cons (s e : Nat) (ss es : List Nat) :
    code (s :: ss) (e :: es) = e * s + code ss es := rfl

def codeImpl : List Nat → List Nat → Nat
  | s :: ss, e :: es => Nat.add (Nat.mul e s) (codeImpl ss es)
  | _, _ => 0

@[csimp] theorem code_eq_impl : code = codeImpl := by
  funext ss es
  induction ss generalizing es with
  | nil => cases es <;> rfl
  | cons s ss ih => cases es <;> simp_all [code, codeImpl]

/-- Evaluate the original tree at the Kronecker substitution. -/
def evalKron (base : Nat) (strides : List Nat) (e : Expr) : Int :=
  Expr.rec (fun z => z) (fun i => power (Int.ofNat base) (strides.getD i 0))
    (fun _ _ a b => Int.add a b) (fun _ _ a b => Int.sub a b)
    (fun _ a => Int.neg a) (fun _ _ a b => Int.mul a b) (fun _ n a => power a n) e

/-- Pack a supplied support directly, without filling the dense box. The public
checks validate exponent lists before calling this evaluator. -/
noncomputable def packTerms (base : Nat) (strides : List Nat)
    (ts : Hex.MvPoly.Kernel.PolyList Int) : Int :=
  List.rec 0 (fun (e, c) _ rest =>
    Int.add (Int.mul c (power (Int.ofNat base) (code strides e))) rest) ts

@[simp] theorem packTerms_nil (base : Nat) (ss : List Nat) : packTerms base ss [] = 0 := rfl
@[simp] theorem packTerms_cons (base : Nat) (ss e : List Nat) (c : Int)
    (ts : Hex.MvPoly.Kernel.PolyList Int) :
    packTerms base ss ((e,c)::ts) = c * power (Int.ofNat base) (code ss e) + packTerms base ss ts := rfl

def packTermsImpl (base : Nat) (strides : List Nat) : Hex.MvPoly.Kernel.PolyList Int → Int
  | [] => 0
  | (e, c) :: ts => Int.add (Int.mul c (power (Int.ofNat base) (code strides e)))
      (packTermsImpl base strides ts)

@[csimp] theorem packTerms_eq_impl : packTerms = packTermsImpl := by
  funext base ss ts
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t; simp_all [packTerms, packTermsImpl]

end Hex.Kronecker
