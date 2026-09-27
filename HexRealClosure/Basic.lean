/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.SelectedSigns
public import HexSignDet.Reencode
public import HexSturm.Basic

public section

/-! Rational selected-root expressions. These are unreduced expressions: checked
sign determination is exposed separately because the producer currently returns
`Except BuildError`. Canonical-zero storage requires its total-success bridge. -/
namespace Hex.RealClosure

/-- A checked descriptor bound to an immutable rational-base context version. -/
abbrev Root (context : Nat) :=
  SignDet.Descriptor Rat Nat Sturm.orderSign context

/-- Validate untrusted root-selection input in its exact context. -/
@[expose] def Root.validate (context : Nat) (raw : SignDet.RawDescriptor Rat Nat) :
    Option (Root context) :=
  SignDet.Descriptor.validate Sturm.orderSign context raw

/-- An old descriptor cannot be validated in a different context version. -/
theorem Root.validate_context {context : Nat} (raw : SignDet.RawDescriptor Rat Nat)
    (h : raw.context ≠ context) : Root.validate context raw = none := by
  unfold Root.validate
  cases hv : SignDet.Descriptor.validate Sturm.orderSign context raw with
  | none => rfl
  | some d =>
    have hb := (SignDet.Descriptor.validate_eq_some.mp hv)
    rw [SignDet.Descriptor.build_context h] at hb
    cases hb

/-- A checked conversion to a new rational-base context version. Validation
is rerun with the new literal binding; the old descriptor remains unchanged. -/
structure Rebinding {context : Nat} (source : Root context) (version : Nat) where
  target : Root version
  checked : Root.validate version { source.raw with context := version } = some target

/-- Revalidate root selection under a new context version. -/
@[expose] def Root.rebind? {context : Nat} (source : Root context) (version : Nat) :
    Option (Rebinding source version) :=
  match h : Root.validate version { source.raw with context := version } with
  | none => none
  | some target => some ⟨target, h⟩

/-- A polynomial expression at the selected root. Distinct expressions may
denote the same value; this type carries no field instance. -/
structure Expression {context : Nat} (d : Root context) where
  polynomial : DensePoly Rat

namespace Expression

@[expose] def ofPoly {context : Nat} {d : Root context} (p : DensePoly Rat) : Expression d := ⟨p⟩
@[expose] def zero {context : Nat} {d : Root context} : Expression d := ⟨0⟩
@[expose] def one {context : Nat} {d : Root context} : Expression d := ⟨1⟩
@[expose] def add {context : Nat} {d : Root context} (a b : Expression d) : Expression d :=
  ⟨a.polynomial + b.polynomial⟩
@[expose] def neg {context : Nat} {d : Root context} (a : Expression d) : Expression d :=
  ⟨-a.polynomial⟩
@[expose] def sub {context : Nat} {d : Root context} (a b : Expression d) : Expression d :=
  ⟨a.polynomial - b.polynomial⟩
@[expose] def mul {context : Nat} {d : Root context} (a b : Expression d) : Expression d :=
  ⟨a.polynomial * b.polynomial⟩

/-- Return a checked sign or the producer's actual diagnostic. This does not
replace a missing total-success theorem by an arbitrary default sign. -/
@[expose] def sign? {context : Nat} {d : Root context} (a : Expression d) :
    Except SignDet.BuildError Int := do
  let signs ← d.buildSigns [a.polynomial]
  return signs.value

/-- Return the monic gcd and its cofactor. For a value nonzero at the selected
root, that root lies in the cofactor. The descriptor remains unchanged. -/
@[expose] def inverseFactor {context : Nat} {d : Root context}
    (a : Expression d) : DensePoly Rat × DensePoly Rat :=
  let g := DensePoly.monicize (DensePoly.gcd d.raw.head a.polynomial)
  (g, (DensePoly.divMod d.raw.head g).1)

/-- Scale the one-sided Bézout coefficient by its computed constant gcd. -/
@[expose] def inverseCandidate {context : Nat} {d : Root context}
    (a : Expression d) : Expression d :=
  let h := a.inverseFactor.2
  let eg := DensePoly.xgcdLeft a.polynomial h
  ⟨DensePoly.scale eg.gcd.leadingCoeff⁻¹ eg.left⟩

/-- Check the Bézout candidate at the selected root. A failed producer remains
an error, distinct from a failed product check. -/
inductive InverseError where
  | build (error : SignDet.BuildError)
  | candidate
  deriving DecidableEq, Repr

/-- Return `none` only for a checked zero operand; report failure of either
sign construction or candidate verification explicitly. -/
@[expose] def inverse? {context : Nat} {d : Root context} (a : Expression d) :
    Except InverseError (Option (Expression d)) :=
  match a.sign? with
  | .error err => .error (.build err)
  | .ok sa =>
    if sa = 0 then .ok none
    else
      let candidate := a.inverseCandidate
      match (sub (mul a candidate) one).sign? with
      | .error err => .error (.build err)
      | .ok sc => if sc = 0 then .ok (some candidate) else .error .candidate

/-- The checked zero branch returns no inverse. -/
theorem inverse?_zero {context : Nat} {d : Root context} (a : Expression d)
    (h : a.sign? = .ok 0) : a.inverse? = .ok none := by
  simp [inverse?, h]

/-- Repack the same polynomial under checked selected-root re-encoding. -/
@[expose] def transport {context : Nat} {d : Root context} {head : DensePoly Rat}
    {lower upper : Endpoint Rat}
    (r : SignDet.Reencoding d head lower upper) (a : Expression d) :
    Expression r.target := ⟨a.polynomial⟩

/-- Copy a stored rational polynomial through checked context rebinding. -/
@[expose] def rebind {context version : Nat} {d : Root context}
    (r : Rebinding d version) (a : Expression d) : Expression r.target :=
  ⟨a.polynomial⟩

end Expression

/-- A checked head change followed by checked context rebinding. -/
structure Refinement {context : Nat} (source : Root context)
    (head : DensePoly Rat) (lower upper : Endpoint Rat) (version : Nat) where
  encoding : SignDet.Reencoding source head lower upper
  binding : Rebinding encoding.target version

/-- Check whether the cofactor contains the selected root, then move it to a
new context version in one checked conversion. -/
@[expose] def Expression.split? {context : Nat} {d : Root context}
    (a : Expression d) (version : Nat) (lower upper : Endpoint Rat) :
    Except SignDet.BuildError
      (Option (Refinement d a.inverseFactor.2 lower upper version)) :=
  match d.buildReencoding a.inverseFactor.2 lower upper with
  | .error err => .error err
  | .ok none => .ok none
  | .ok (some encoding) =>
    match Root.rebind? encoding.target version with
    | none => .ok none
    | some binding => .ok (some ⟨encoding, binding⟩)

/-- Transport a value through both checks of a rational refinement. -/
@[expose] def Expression.refine {context version : Nat} {d : Root context}
    {head : DensePoly Rat} {lower upper : Endpoint Rat}
    (r : Refinement d head lower upper version) (a : Expression d) :
    Expression r.binding.target :=
  rebind r.binding (transport r.encoding a)

end Hex.RealClosure
