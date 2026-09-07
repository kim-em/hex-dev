module

public import HexRationalFn
public meta import HexRationalFn

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

end HexRationalFn.Conformance
