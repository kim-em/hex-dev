/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn
public import HexRationalFn.Domains
public meta import HexRationalFn
public meta import HexRationalFn.Domains

public section

/-!
Oracle: SymPy rational-function domains (external fixtures), algebraic identities here.
Mode: always for these deterministic checks.

Covered operations: canonical construction, equality, addition, subtraction,
multiplication, inversion, checked division, natural powers and coefficient-field use.
Covered properties: canonical pair agreement, field laws, plan independence,
polynomial division and Bézout identities over the rational-function field.
Covered edge cases: zero denominators, nonmonic denominators, cancelled common
factors, shared denominators, zero and negative powers, and zero divisors.
-/

namespace HexRationalFn.Conformance

open Hex

private def x : RationalFn Rat := RationalFn.X

private def fraction (p q : List Rat) : Option (RationalFn Rat) :=
  RationalFn.ofFraction? (DensePoly.ofList p) (DensePoly.ofList q)

#guard fraction [0] [0] = none
#guard fraction [1] [0] = none
#guard fraction [0] [-3, 1] = some 0
#guard fraction [-1, 0, 1] [-1, 1] = some (x + 1)
#guard fraction [-2, -2] [-2] = some (x + 1)
#guard fraction [2] [4] = some (RationalFn.C (1 / 2 : Rat))
#guard (x + 1) * (x - 1) = x ^ (2 : Nat) - 1
#guard (x + 1) / (x + 1) = 1
#guard x / 0 = 0
#guard RationalFn.div? (0 : RationalFn Rat) 0 = none
#guard RationalFn.inv? (0 : RationalFn Rat) = none
#guard (0 : RationalFn Rat) ^ (0 : Nat) = 1
#guard (x / (x + 1)) ^ (3 : Nat) = x ^ (3 : Nat) / (x + 1) ^ (3 : Nat)
#guard x ^ (-2 : Int) = 1 / x ^ (2 : Nat)
#guard let h := (x + 1) ^ (16 : Nat)
  (h * (x ^ (2 : Nat) + 1)) / (h * x) = (x ^ (2 : Nat) + 1) / x
#guard 1 / x + (-1 / x) = 0
#guard 1 / x + 1 / (x + 1) = (2 * x + 1) / (x * (x + 1))
#guard 1 / (x * (x + 1)) + 1 / (x * (x - 1)) = 2 / (x ^ (2 : Nat) - 1)
#guard ((x + 1) / x) * (x / (x - 1)) = (x + 1) / (x - 1)
#guard RationalFn.addWith DensePoly.schoolbookPlan (1 / x) (1 / (x + 1)) =
  1 / x + 1 / (x + 1)
#guard RationalFn.mulWith (DensePoly.karatsubaPlan 2) ((x + 1) / x) (x / (x - 1)) =
  (x + 1) / (x - 1)

#guard RationalFn.eval? (1 / x) 0 = none
#guard RationalFn.eval? ((x ^ (2 : Nat) - 1) / (x - 1)) 1 = some 2
#guard RationalFn.eval? (1 / x + (-1 / x)) 0 = some 0
#guard RationalFn.eval? (0 : RationalFn Rat) 0 = some 0
#guard RationalFn.eval? ((x + 1) / (x - 1)) 2 = some 3

#guard RationalFn.derivative (x ^ (3 : Nat)) = 3 * x ^ (2 : Nat)
#guard RationalFn.derivative (1 / x) = -1 / x ^ (2 : Nat)
#guard RationalFn.derivative (0 : RationalFn Rat) = 0
#guard RationalFn.derivative ((x ^ (2 : Nat) - 1) / (x - 1)) = 1
#guard RationalFn.split ((x ^ (2 : Nat) + 1) / x) = (DensePoly.ofList [0, 1], 1 / x)
#guard RationalFn.split (0 : RationalFn Rat) = (0, 0)
#guard RationalFn.split (x + 1) = (DensePoly.ofList [1, 1], 0)
#guard RationalFn.toPoly? (x + 1) = some (DensePoly.ofList [1, 1])
#guard RationalFn.toPoly? (1 / x) = none
#guard RationalFn.toPoly? (0 : RationalFn Rat) = some 0

private def cert : RationalFn.Cert Rat :=
  ⟨DensePoly.ofList [1, 1], 1, 0, 1⟩

#guard RationalFn.check (DensePoly.ofList [-1, 0, 1]) (DensePoly.ofList [-1, 1]) cert
#guard !(RationalFn.check (DensePoly.ofList [-1, 0, 1]) (DensePoly.ofList [-1, 1])
  { cert with num := DensePoly.ofList [2, 1] })
#guard !(RationalFn.check (DensePoly.ofList [-1, 0, 1]) (DensePoly.ofList [-1, 1])
  { cert with t := 2 })
#guard let p : DensePoly Rat := DensePoly.ofList [1, 2, 1]
  let q : DensePoly Rat := DensePoly.ofList [0, 1, 1]
  RationalFn.check p q (RationalFn.certifyWith RationalFn.defaultPlan p q (by decide))

example : RationalFn.check (DensePoly.ofList [-1, 0, 1]) (DensePoly.ofList [-1, 1]) cert = true :=
  by decide +kernel

private def outer : DensePoly (RationalFn Rat) := DensePoly.ofList [x, 1]
private def divisor : DensePoly (RationalFn Rat) := DensePoly.ofList [1 / x, 1]

#guard let qr := DensePoly.divMod (outer * divisor) divisor
  qr.1 = outer ∧ qr.2 = 0
#guard let r := DensePoly.xgcd outer divisor
  r.left * outer + r.right * divisor = r.gcd

#guard let y : RationalFn (ZMod64 2) := RationalFn.X
  RationalFn.derivative (y ^ (2 : Nat)) = 0 ∧ y ^ (2 : Nat) - y ≠ 0 ∧
    ([0, 1] : List (ZMod64 2)).all (fun a => RationalFn.eval? (y ^ (2 : Nat) - y) a == some 0)
#guard let y : RationalFn (ZMod64 7) := RationalFn.X
  RationalFn.derivative (y ^ (7 : Nat)) = 0 ∧ y ^ (7 : Nat) - y ≠ 0 ∧
    (List.range 7).all (fun a => RationalFn.eval? (y ^ (7 : Nat) - y) (ZMod64.ofNat 7 a) == some 0)
#guard let y : RationalFn (ZMod64 2) := RationalFn.X
  (y + 1) / (y + 1) = 1 ∧ 1 / y + 1 / y = 0 ∧ RationalFn.eval? (1 / y) 0 = none

#guard let y : RationalFn (ZMod64 7) := RationalFn.X
  let f := (y ^ (8 : Nat) + 1) / (y + 1)
  let g := (y + 1) / (y ^ (8 : Nat) + 1)
  RationalFn.mulWith (DensePoly.karatsubaPlan 1) f g =
    RationalFn.mulWith DensePoly.schoolbookPlan f g

#guard !(RationalFn.check (DensePoly.ofList [-1, 0, 1] : DensePoly Rat) (DensePoly.ofList [-1, 1])
  ⟨DensePoly.ofList [-1, 0, 1], DensePoly.ofList [-1, 1], 0, 1⟩)
#guard !(RationalFn.check (DensePoly.ofList [-1, 0, 1] : DensePoly Rat) (DensePoly.ofList [-1, 1])
  ⟨DensePoly.ofList [2, 2], 2, 0, DensePoly.C (1 / 2)⟩)
#guard RationalFn.check (DensePoly.ofList [-1, 0, 1] : DensePoly Rat) (DensePoly.ofList [-1, 1])
  ⟨DensePoly.ofList [1, 1], 1, 1, DensePoly.ofList [0, -1]⟩

#guard let p : DensePoly Rat := #p[1, 1]
  let q : DensePoly Rat := #p[0, 1]
  let c : RationalFn.Cert Rat := ⟨p, q, 1, -1⟩
  RationalFn.check p q c &&
    !(RationalFn.check p q { c with s := 2 }) &&
    !(RationalFn.check p q { c with den := q + 1 })

private def samples : List (RationalFn Rat) := [0, 1, x, 1 / x, (x + 1) / (x - 1)]

#guard samples.all fun f =>
  decide (-(-f) = f ∧ f⁻¹⁻¹ = f ∧ f ^ (0 : Nat) = 1 ∧ f ^ (1 : Nat) = f ∧
    f ^ (2 : Nat) = f * f ∧ RationalFn.powWith (DensePoly.karatsubaPlan 1) f 3 = f ^ (3 : Nat))

#guard samples.all fun f => samples.all fun g =>
  decide (f + g = g + f ∧ f * g = g * f ∧ f - g = f + (-g) ∧ f / g = f * g⁻¹ ∧
    RationalFn.addWith (DensePoly.karatsubaPlan 1) f g = f + g ∧
    RationalFn.subWith (DensePoly.karatsubaPlan 1) f g = f - g ∧
    RationalFn.mulWith (DensePoly.karatsubaPlan 1) f g = f * g ∧
    RationalFn.divWith (DensePoly.karatsubaPlan 1) f g = f / g ∧
    RationalFn.div? f g = if g = 0 then none else some (f / g))

#guard samples.all fun f =>
  let c := RationalFn.certifyWith DensePoly.schoolbookPlan f.num f.den f.den_ne_zero
  decide (RationalFn.ofCert? f.num f.den c = some f ∧
    RationalFn.ofCert? f.num f.den { c with den := 0 } = none ∧
    RationalFn.inv? f = (if f = 0 then none else some f⁻¹) ∧
    RationalFn.normalizeWith (DensePoly.karatsubaPlan 1) f.num f.den f.den_ne_zero = f ∧
    RationalFn.derivativeWith (DensePoly.karatsubaPlan 1) f = RationalFn.derivative f ∧
    RationalFn.splitWith (DensePoly.karatsubaPlan 1) f = RationalFn.split f)

end HexRationalFn.Conformance
