/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseContext

public section

namespace Hex.RealClosure.BaseContext

/-- Finite recursive coefficient data. Fractions belong to one extension level. -/
inductive Syntax where
  | rational (value : Rat)
  | fraction (numerator denominator : List Syntax)
  deriving Repr

@[expose] def writeFraction {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (write : K → Syntax) (f : RationalFn K) : Syntax :=
  .fraction (f.num.toArray.toList.map write) (f.den.toArray.toList.map write)

@[expose] def readFraction {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (read : Syntax → Option K) : Syntax → Option (RationalFn K)
  | .rational _ => none
  | .fraction numerator denominator => do
    let p ← numerator.mapM read
    let q ← denominator.mapM read
    RationalFn.ofFraction? (DensePoly.ofCoeffs p.toArray) (DensePoly.ofCoeffs q.toArray)

/-- Print every coefficient through its exact real predecessor. -/
@[expose] def RealChain.write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → OrderedFn.Oracle.Bounds}
    {sign : K → Int} (context : RealChain registry K approx sign) : K → Syntax := by
  cases context with
  | base => exact Syntax.rational
  | step parent key bounds registered sp ap => exact writeFraction parent.write

/-- Check recursive level shape and every denominator; use the canonical
fraction constructor after reading predecessor coefficients. -/
@[expose] def RealChain.read {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → OrderedFn.Oracle.Bounds}
    {sign : K → Int} (context : RealChain registry K approx sign) : Syntax → Option K := by
  cases context with
  | base => exact fun raw => match raw with
      | .rational q => some q
      | .fraction _ _ => none
  | step parent key bounds registered sp ap => exact readFraction parent.read

@[expose] def Chain.write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Chain registry K sign) : K → Syntax := by
  cases context with
  | real parent => exact parent.write
  | infinitesimal parent => exact writeFraction parent.write

@[expose] def Chain.read {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Chain registry K sign) : Syntax → Option K := by
  cases context with
  | real parent => exact parent.read
  | infinitesimal parent => exact readFraction parent.read

private theorem mapM_roundtrip {K : Type} (write : K → Syntax)
    (read : Syntax → Option K) (h : ∀ a, read (write a) = some a) (xs : List K) :
    (xs.map write).mapM read = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [h, ih]

private theorem fraction_roundtrip {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (write : K → Syntax) (read : Syntax → Option K)
    (h : ∀ a, read (write a) = some a) (f : RationalFn K) :
    readFraction read (writeFraction write f) = some f := by
  simp only [writeFraction, readFraction, mapM_roundtrip write read h,
    bind, Option.bind, Array.toArray_toList, DensePoly.ofCoeffs_toArray]
  rw [RationalFn.ofFraction?_eq_some _ _ f.den_ne_zero, RationalFn.normalize_self]

theorem RealChain.read_write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {approx : K → Rat → OrderedFn.Oracle.Bounds}
    {sign : K → Int} (context : RealChain registry K approx sign) (a : K) :
    context.read (context.write a) = some a := by
  induction context with
  | base => rfl
  | step parent key bounds registered sp ap ih => exact fraction_roundtrip _ _ ih a

theorem Chain.read_write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Chain registry K sign) (a : K) :
    context.read (context.write a) = some a := by
  induction context with
  | real parent => exact parent.read_write a
  | infinitesimal parent ih => exact fraction_roundtrip _ _ ih a

@[expose] def Context.write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : K → Syntax := context.chain.write

@[expose] def Context.read {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) : Syntax → Option K := context.chain.read

theorem Context.read_write {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (context : Context registry K sign) (a : K) : context.read (context.write a) = some a :=
  context.chain.read_write a

/-- A value's full literal base-context binding and finite recursive payload.
The registry is fixed by the application of the reader. -/
structure Serialized where
  binding : Signature
  value : Syntax
  deriving Repr

namespace Element

variable {registry : Registry} {K : Type} [Lean.Grind.Field K] [DecidableEq K]
variable {baseSign : K → Int} {context : Context registry K baseSign}

@[expose] def write (a : Element context) : Serialized :=
  ⟨context.signature, context.write a.stored⟩

/-- Reject incompatible bindings before reading any coefficient data. -/
@[expose] def read (context : Context registry K baseSign) (raw : Serialized) :
    Option (Element context) :=
  if raw.binding = context.signature then (context.read raw.value).map Element.mk else none

theorem read_write (a : Element context) : read context a.write = some a := by
  simp [read, write, Context.read_write]

theorem read_stale (raw : Serialized) (h : raw.binding ≠ context.signature) :
    read context raw = none := by simp [read, h]

end Element
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Element.read_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.read_write
/-- info: 'Hex.RealClosure.BaseContext.Element.read_stale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.BaseContext.Element.read_stale
