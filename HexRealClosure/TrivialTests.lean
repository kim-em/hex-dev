/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Trivial

namespace Hex.RealClosure.Trivial.Tests

private def require (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)

private def same (a b : RealRootSet) : Bool :=
  match a, b with
  | .all, .all => true
  | .finite left, .finite right =>
    left.map (fun e => (e.root, e.multiplicity)) == right.map (fun e => (e.root, e.multiplicity))
  | _, _ => false

private def check (name : String) (p : DensePoly Rat) : IO Unit := do
  let generic := Roots.roots Sturm.orderSign 42 p
  let converted := output generic
  let backend := (polynomial p).roots
  require (same converted backend) s!"generic/backend roots differ: {name}"
  require (same (roots 42 p) backend) s!"public root conversion differs: {name}"
  match generic with
  | .all => require p.isZero s!"unexpected all-roots output: {name}"
  | .finite entries =>
    for a in entries do
      for b in entries do
        let .ok order := a.root.compare b.root
          | throw (IO.userError s!"generic comparison failed: {name}")
        require (order == compare a.root b.root) s!"generic/backend comparison differs: {name}"

private def run : IO Unit := do
  let x : DensePoly Rat := DensePoly.ofCoeffs #[0, 1]
  let square := x * x - DensePoly.C 2
  let linear := x - DensePoly.C 1
  check "zero" 0
  check "constant" (DensePoly.C 7)
  check "zero multiplicity" (x * x * x * x)
  check "irrational pair" square
  check "Yun multiplicities across factors" (square * square * linear * linear * linear)
  check "nonmonic negative scale" (DensePoly.scale (-3) (DensePoly.scale 2 (x * x) - 1))
  check "distinct rational roots and multiplicities"
    (linear * linear * linear * (x + DensePoly.C 2) * (x + DensePoly.C 2))
  check "non-dyadic rational and irrational roots" ((x - DensePoly.C (1 / 3)) * square)
  IO.println "generic rational roots and comparisons agree with the real-algebraic backend"

#eval run

end Hex.RealClosure.Trivial.Tests
