/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealClosure.Element
public import HexPoly.Lcm

public section

/-!
# Yun decomposition

The executable recurrence uses the ordinary dense-polynomial operations. The
raw version supports tower coefficients whose stored equality is not value
equality. The public version requires an ordered field, hence characteristic
zero. Their correctness theorems belong in the Mathlib companion.
-/

namespace Hex.RealClosure.Yun

universe u

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Zero is kept separate from the scalar-times-factors result. -/
inductive Decomposition (K : Type u) [Zero K] [DecidableEq K] where
  | zero
  | factors (unit : K) (entries : Array (DensePoly K × Nat))

/-- The Yun recurrence. `v` contains factors whose multiplicity is at least
`multiplicity`; `w` is the derivative quotient carried between rounds. The
original degree bounds the fuel, including rounds that emit no factor. -/
@[expose] def loop {K : Type u} [Zero K] [One K] [Add K] [Sub K]
    [Mul K] [Div K] [Inv K] [NatCast K] [DecidableEq K]
    (v w : DensePoly K) (multiplicity fuel : Nat)
    (out : Array (DensePoly K × Nat)) : Array (DensePoly K × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if v.natDegree = 0 then out
      else
        let t := w - DensePoly.derivativeImpl v
        let z := DensePoly.monicize (DensePoly.gcd v t)
        let out := if 0 < z.natDegree then out.push (z, multiplicity) else out
        loop (v / z) (t / z) (multiplicity + 1) fuel out

/-- Run the recurrence on raw coefficients whose operations need not satisfy
field laws as literal equality. The companion must supply an interpretation
into an ordered field before claiming multiplicity correctness. -/
@[expose] def decomposeRaw {K : Type u} [Zero K] [One K] [Add K] [Sub K]
    [Mul K] [Div K] [Inv K] [NatCast K] [DecidableEq K]
    (f : DensePoly K) : Decomposition K :=
  if f.isZero then .zero
  else if f.natDegree = 0 then .factors f.leadingCoeff #[]
  else
    let a := DensePoly.monicize
      (DensePoly.gcd f (DensePoly.derivativeImpl f))
    let v := f / a
    let w := DensePoly.derivativeImpl f / a
    .factors f.leadingCoeff (loop v w 1 (f.natDegree + 1) #[])

@[simp] theorem decomposeRaw_zero {K : Type u} [Zero K] [One K]
    [Add K] [Sub K] [Mul K] [Div K] [Inv K] [NatCast K]
    [DecidableEq K] :
    decomposeRaw (0 : DensePoly K) = .zero := by
  have hz : DensePoly.isZero (0 : DensePoly K) = true := by rfl
  simp [decomposeRaw, hz]

theorem decomposeRaw_constant {K : Type u} [Zero K] [One K]
    [Add K] [Sub K] [Mul K] [Div K] [Inv K] [NatCast K]
    [DecidableEq K] (f : DensePoly K)
    (hzero : f.isZero = false) (hdegree : f.natDegree = 0) :
    decomposeRaw f = .factors f.leadingCoeff #[] := by
  simp [decomposeRaw, hzero, hdegree]

/-- Yun's recurrence over a lawful ordered field. Zero has its own result;
nonzero constants return their scalar and an empty factor list. -/
@[expose] def decompose {K : Type u} [Lean.Grind.Field K]
    [LE K] [LT K] [Std.IsPreorder K]
    [Lean.Grind.OrderedRing K] [DecidableEq K]
    (f : DensePoly K) : Decomposition K :=
  decomposeRaw f

/-- Reconstruct the polynomial denoted by a scalar and multiplicity factors.
This is also useful to independently check a computed result. -/
@[expose] def reconstruct {K : Type u} [Lean.Grind.CommRing K]
    [DecidableEq K] (unit : K)
    (entries : Array (DensePoly K × Nat)) : DensePoly K :=
  entries.foldl (fun product entry => product * entry.1 ^ entry.2)
    (DensePoly.C unit)

/-- Degree accounted for by the emitted factors. -/
@[expose] def degreeSum {K : Type u} [Zero K] [DecidableEq K]
    (entries : Array (DensePoly K × Nat)) : Nat :=
  entries.foldl (fun degree entry =>
    degree + entry.2 * entry.1.natDegree) 0

end Hex.RealClosure.Yun
