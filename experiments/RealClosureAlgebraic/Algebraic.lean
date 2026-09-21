/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealRoots.Var

/-! A single selected algebraic root. Descriptors are checked at the experiment
boundary; no arbitrary descriptor is claimed to provide a field. -/
namespace Algebraic
open Hex
abbrev QPoly := DensePoly Rat

structure Descriptor where
  polynomial : QPoly
  interval : DyadicInterval

def rootCount (p : QPoly) (i : DyadicInterval) : Int :=
  (ZPoly.ratPolyPrimitivePart p).sturmCount i

def valid (d : Descriptor) : Bool :=
  d.polynomial.natDegree > 0 &&
  (DensePoly.gcd d.polynomial d.polynomial.derivative).natDegree == 0 &&
  ZPoly.evalDyadic (ZPoly.ratPolyPrimitivePart d.polynomial) d.interval.lower != 0 &&
  ZPoly.evalDyadic (ZPoly.ratPolyPrimitivePart d.polynomial) d.interval.upper != 0 &&
  rootCount d.polynomial d.interval == 1

structure Cost where
  zeroTests : Nat := 0
  gcds : Nat := 0
  sturmCounts : Nat := 0
deriving Repr, BEq
instance : Add Cost := ⟨fun a b =>
  ⟨a.zeroTests+b.zeroTests, a.gcds+b.gcds, a.sturmCounts+b.sturmCounts⟩⟩

/-- Fast zero/constant remainders avoid gcd; other cases use actual gcd and Sturm. -/
def zeroWithCost (d : Descriptor) (q : QPoly) : Bool × Cost :=
  let r := (DensePoly.divMod q d.polynomial).2
  if r.isZero then (true, ⟨1,0,0⟩)
  else if r.natDegree == 0 then (false, ⟨1,0,0⟩)
  else
    let g := DensePoly.gcd d.polynomial r
    if g.natDegree == 0 then (false, ⟨1,1,0⟩)
    else (rootCount g d.interval == 1, ⟨1,1,1⟩)

def isZero (d : Descriptor) (q : QPoly) : Bool := (zeroWithCost d q).1

/-- Nonzero representatives are deliberately not reduced modulo the defining polynomial. -/
abbrev Element (d : Descriptor) := Option {q : QPoly // isZero d q = false}
instance (d : Descriptor) : Zero (Element d) := ⟨none⟩
instance (d : Descriptor) : DecidableEq (Element d) :=
  inferInstanceAs (DecidableEq (Option {q : QPoly // isZero d q = false}))
def pack (d : Descriptor) (q : QPoly) : Element d :=
  if h : isZero d q = false then some ⟨q,h⟩ else none
def raw {d : Descriptor} : Element d → QPoly
  | none => 0
  | some q => q.val

instance (d : Descriptor) : One (Element d) := ⟨pack d 1⟩
instance (d : Descriptor) : NatCast (Element d) := ⟨fun n => pack d (DensePoly.C n)⟩
instance (d : Descriptor) : Add (Element d) := ⟨fun a b => pack d (raw a + raw b)⟩
instance (d : Descriptor) : Neg (Element d) := ⟨fun a => pack d (-raw a)⟩
instance (d : Descriptor) : Sub (Element d) := ⟨fun a b => pack d (raw a - raw b)⟩
instance (d : Descriptor) : Mul (Element d) := ⟨fun a b => pack d (raw a * raw b)⟩

structure Inverse where
  value : QPoly
  polynomial : QPoly
  discarded : QPoly
  split : Bool

/-- A nonzero element is inverted modulo the factor containing the selected root.
The full xgcd is computed only after a plain gcd identifies that factor. -/
def invert (d : Descriptor) (q : QPoly) : Inverse :=
  if isZero d q then ⟨0,d.polynomial,1,false⟩ else
    let g := DensePoly.monicize (DensePoly.gcd d.polynomial q)
    let h := (DensePoly.divMod d.polynomial g).1
    let eg := DensePoly.xgcd q h
    ⟨DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left, h, g, g.natDegree > 0⟩

instance (d : Descriptor) : Inv (Element d) := ⟨fun a => pack d (invert d (raw a)).value⟩
instance (d : Descriptor) : Div (Element d) := ⟨fun a b => a * b⁻¹⟩

/-- A split returns a different coefficient type. All live values are explicitly repacked. -/
def refine (d : Descriptor) (i : Inverse) : Descriptor := ⟨i.polynomial,d.interval⟩
def transport (d e : Descriptor) (a : Element d) : Element e := pack e (raw a)

def sqrt2 : QPoly := DensePoly.ofCoeffs #[-2,0,1]
def sqrt3 : QPoly := DensePoly.ofCoeffs #[-3,0,1]
def interval : DyadicInterval := ⟨1, (Dyadic.ofInt 3) >>> (1 : Int), by decide⟩
def irreducible : Descriptor := ⟨sqrt2, interval⟩
def reducible : Descriptor := ⟨sqrt2 * sqrt3, interval⟩

/-- Independent reference in Q(sqrt(2)); used only in validation/output hashing.
It is not used by the selected-root zero test or inversion. -/
def canonical (q : QPoly) : QPoly := (DensePoly.divMod q sqrt2).2
def observe {d : Descriptor} (a : Element d) : Array Rat := (canonical (raw a)).toArray
def observePoly {d : Descriptor} (p : DensePoly (Element d)) : Array (Array Rat) :=
  p.toArray.map observe

/-- Exact sign in this particular quadratic field; a generic tower sign is out of scope. -/
def signSqrt2 (q : QPoly) : Int :=
  let r := canonical q
  let a := r.coeff 0
  let b := r.coeff 1
  if b == 0 then a.num.sign
  else if a == 0 then b.num.sign
  else if a.num.sign == b.num.sign then a.num.sign
  else if a*a > 2*b*b then a.num.sign else b.num.sign

/-- Experimental comparison arm: use the existing convolution over raw polynomials,
then normalize selected-root zeros once per output coefficient. -/
def batchMul (d : Descriptor) (p q : DensePoly (Element d)) : DensePoly (Element d) :=
  let a := DensePoly.ofCoeffs (p.toArray.map raw)
  let b := DensePoly.ofCoeffs (q.toArray.map raw)
  DensePoly.ofCoeffs ((a*b).toArray.map (pack d))

/-- Instrumentation-only shadow of the same row-major convolution. Each call to
zeroWithCost is the actual zero procedure. Counts do not enter timed kernels. -/
def tracedMul (d : Descriptor) (batch : Bool)
    (p q : DensePoly (Element d)) : DensePoly (Element d) × Cost := Id.run do
  if p.isZero || q.isZero then return (0,{})
  let mut out : Array QPoly := Array.replicate (p.size+q.size-1) 0
  let mut cost : Cost := {}
  for i in [:p.size] do
    for j in [:q.size] do
      let mut prod := raw (p.coeff i) * raw (q.coeff j)
      if !batch then
        let (z,c) := zeroWithCost d prod
        cost := cost+c
        if z then prod := 0
      let mut sum := out.getD (i+j) 0 + prod
      if !batch then
        let (z,c) := zeroWithCost d sum
        cost := cost+c
        if z then sum := 0
      out := out.set! (i+j) sum
  if batch then
    -- Match the raw DensePoly product: it trims literal trailing zeros first.
    out := (DensePoly.ofCoeffs out).toArray
    for a in out do cost := cost+(zeroWithCost d a).2
  return (DensePoly.ofCoeffs (out.map (pack d)), cost)

def input (d : Descriptor) (n : Nat) (salt : Nat := 0) : DensePoly (Element d) :=
  DensePoly.ofCoeffs ((List.range n).toArray.map fun i =>
    pack d ((DensePoly.ofCoeffs #[(((i+salt)%5+1 : Nat) : Rat),
      (((i+salt)%3+1 : Nat) : Rat)] : QPoly) +
      DensePoly.scale ((i%2+1 : Nat) : Rat) sqrt2))

end Algebraic
