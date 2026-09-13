/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMinPoly.Producer
public import HexMatrix.Scaled

public section

/-! Integer list certificates for rational matrix minimal polynomials. -/

namespace Hex.Matrix

open Lists

/-- A vector order and a right inverse, each with its own denominator. -/
structure OrderWitness where
  poly : Scaled
  deg : Nat
  inv : ScaledRows
  deriving Repr, Inhabited, DecidableEq

/-- The six polynomial blocks of a reference LCM certificate. -/
structure LcmWitness where
  common : Scaled
  left : Scaled
  right : Scaled
  bezoutLeft : Scaled
  bezoutRight : Scaled
  result : Scaled
  deriving Repr, Inhabited, DecidableEq

/-- A basis-wide minimal-polynomial witness and its scaled input. -/
structure MinPolyWitness where
  input : ScaledRows
  poly : Scaled
  order : List OrderWitness
  steps : List LcmWitness
  deriving Repr, Inhabited, DecidableEq

namespace MinPolyLists

/-- Exact unnormalized integer coefficient addition. -/
@[expose] def add : List Int → List Int → List Int
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => Int.add x y :: add xs ys

/-- Integer coefficient scaling. -/
@[expose] def scale (a : Int) (xs : List Int) : List Int := xs.map (Int.mul a)

/-- Structural integer coefficient convolution. -/
@[expose] def mul : List Int → List Int → List Int
  | [], _ => []
  | x :: xs, ys => add (scale x ys) (0 :: mul xs ys)

/-- Common denominators are cleared once per polynomial operation. -/
@[expose] def addPoly (a b : Scaled) : Scaled :=
  ⟨Nat.mul a.denom b.denom,
    add (scale (Int.ofNat b.denom) a.nums) (scale (Int.ofNat a.denom) b.nums)⟩

/-- Multiplication without rational normalization. -/
@[expose] def mulPoly (a b : Scaled) : Scaled :=
  ⟨Nat.mul a.denom b.denom, mul a.nums b.nums⟩

/-- Equality modulo trailing zero coefficients, by integer cross products. -/
@[expose] def eqPoly (a b : Scaled) : Bool :=
  all (fun i => decide (Int.mul (entry 0 a.nums i) (Int.ofNat b.denom) =
    Int.mul (entry 0 b.nums i) (Int.ofNat a.denom))) (max a.nums.length b.nums.length)

/-- Every supplied polynomial has a positive denominator and normalized length. -/
@[expose] def valid (a : Scaled) : Bool :=
  Nat.blt 0 a.denom &&
    (a.nums.isEmpty || !(decide (entry 0 a.nums (a.nums.length - 1) = 0)))

/-- The leading coefficient is one, including rejection of the zero polynomial. -/
@[expose] def monic (a : Scaled) : Bool :=
  decide (entry 0 a.nums (a.nums.length - 1) = Int.ofNat a.denom)

/-- Integer matrix-vector product, evaluated once per Krylov power. -/
@[expose] def mulVec (z : List (List Int)) (v : List Int) : List Int := z.map (dot · v)

/-- Successive integer powers, starting with the supplied vector. -/
@[expose] def powers (z : List (List Int)) : Nat → List Int → List (List Int)
  | 0, _ => []
  | k + 1, v => v :: powers z k (mulVec z v)

/-- The standard basis vector, as a list. -/
@[expose] def basis (n i : Nat) : List Int := (List.range n).map (fun j => identity i j)

/-- One coordinate of the denominator-cleared polynomial evaluation.
`d` descends from the order degree while the lists ascend in power. -/
@[expose] def evaluate (D : Nat) : Nat → List Int → List Int → Int
  | _, [], _ => 0
  | _, _, [] => 0
  | d, a :: as, v :: vs =>
    Int.add (Int.mul (Int.mul a (Int.ofNat (Nat.pow D d))) v) (evaluate D (d - 1) as vs)

/-- Check a basis order with shared integer Krylov powers. -/
@[expose] def orderCheck (n i : Nat) (z : ScaledRows) (o : OrderWitness) : Bool :=
  Nat.ble o.deg n && valid o.poly && monic o.poly &&
  Nat.beq o.poly.nums.length (o.deg + 1) &&
  Nat.blt 0 o.inv.denom && shape n o.deg o.inv.nums &&
  let K := powers z.nums (o.deg + 1) (basis n i)
  all (fun j => decide (evaluate z.denom o.deg o.poly.nums (column j K) = 0)) n &&
  all (fun k => all (fun j => decide (
    dot (entry [] K k) (column j o.inv.nums) =
      Int.mul (Int.mul (Int.ofNat (Nat.pow z.denom k)) (Int.ofNat o.inv.denom))
        (identity k j))) o.deg) o.deg

/-- Every LCM block is validated before its four identities are checked. -/
@[expose] def stepCheck (running incoming : Scaled) (s : LcmWitness) : Bool :=
  valid s.common && valid s.left && valid s.right && valid s.bezoutLeft &&
  valid s.bezoutRight && valid s.result &&
  eqPoly running (mulPoly s.common s.left) &&
  eqPoly incoming (mulPoly s.common s.right) &&
  eqPoly (addPoly (mulPoly s.bezoutLeft running) (mulPoly s.bezoutRight incoming)) s.common &&
  eqPoly s.result (mulPoly s.left incoming)

/-- The fold verifies exact coverage and returns the final equality check. -/
@[expose] def stepsCheck (final : Scaled) : Scaled → List OrderWitness → List LcmWitness → Bool
  | running, [], [] => eqPoly final running
  | running, o :: os, s :: ss => stepCheck running o.poly s && stepsCheck final s.result os ss
  | _, _, _ => false

end MinPolyLists

/-- Kernel-cheap certificate checking; all polynomial and Krylov arithmetic
uses only integer lists, with no decoded matrix or polynomial reduction. -/
@[expose] def checkMinPolyList (n : Nat) (rows : List (List Rat)) (c : MinPolyWitness) : Bool :=
  Nat.blt 0 c.input.denom && shape n n c.input.nums &&
  scaleRows c.input.denom rows c.input.nums &&
  Nat.beq c.order.length n && Nat.beq c.steps.length n &&
  MinPolyLists.valid c.poly && MinPolyLists.monic c.poly &&
  all (fun i => MinPolyLists.orderCheck n i c.input (entry default c.order i)) n &&
  MinPolyLists.stepsCheck c.poly ⟨1, [1]⟩ c.order c.steps

/-- Reshape a reference certificate; this function runs only in the producer. -/
def MinPolyWitness.ofCert (A : Matrix Rat n n) (c : MinPolyCert Rat n) : MinPolyWitness :=
  let poly (p : DensePoly Rat) := Scaled.encode p.toArray.toList
  let matrix {k l : Nat} (B : Matrix Rat k l) :=
    ScaledRows.encode (B.rows.toList.map (·.toList))
  { input := matrix A
    poly := poly c.poly
    order := c.order.toList.map fun o => ⟨poly o.poly, o.deg, matrix o.inv⟩
    steps := c.steps.toList.map fun s =>
      ⟨poly s.common, poly s.left, poly s.right, poly s.bezoutLeft, poly s.bezoutRight, poly s.result⟩ }

/-- Produce the certificate through the existing compiled basis-wide algorithm. -/
def minPolyWitness (A : Matrix Rat n n) : MinPolyWitness :=
  MinPolyWitness.ofCert A (minPolyCert A)

end Hex.Matrix
