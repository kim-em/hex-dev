/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Init.Data.Dyadic

@[expose] public section

/-!
# Exact interval cuts

This module defines the representation-independent raw data shared by the
`hex-interval` representation experiments.  A finite cut carries its exact
dyadic value and a strictness bit; either side may instead be unbounded.

`Raw.normalize` is the exact canonicalizer for values that have already passed
an endpoint-cost preflight. `Raw.normalizeWithin` is the resource-safe entry
point for untrusted values: it rejects an excessive dyadic height or alignment
shift before comparison can allocate a shifted mantissa. The eventual opaque
`Hex.Interval` backing store will be selected by the D2 measurements; neither
candidate is baked into this module.
-/

namespace Hex.Interval

/-- Rounding precision for the initial dyadic endpoint backend.  Signed
precisions permit coarse grids at large magnitudes. -/
abbrev Precision := Int

/-- A lower interval cut.  For a finite cut, `strict = true` denotes
`value < x`; `false` denotes `value ≤ x`. -/
inductive Lower where
  | unbounded
  | finite (value : Dyadic) (strict : Bool)
  deriving DecidableEq

/-- An upper interval cut.  For a finite cut, `strict = true` denotes
`x < value`; `false` denotes `x ≤ value`. -/
inductive Upper where
  | finite (value : Dyadic) (strict : Bool)
  | unbounded
  deriving DecidableEq

/-- Raw interval data.  `empty` is the unique canonical empty shape; `bounds`
is canonical exactly when its two cuts are consistent. -/
inductive Raw where
  | empty
  | bounds (lower : Lower) (upper : Upper)
  deriving DecidableEq

/-! ## Endpoint comparison preflight -/

/-- Resource limits that must be checked before comparing finite dyadics.
`maxEndpointHeight` bounds mantissa bits plus exponent magnitude;
`maxAlignmentShift` independently bounds the shift used by exact comparison. -/
structure EndpointLimit where
  maxEndpointHeight : Nat
  maxAlignmentShift : Nat
  deriving DecidableEq, Repr

/-- Allocation-independent size data for one canonical dyadic endpoint. -/
structure EndpointCost where
  numeratorBits : Nat
  encodedExponentBits : Nat
  exponentMagnitude : Nat
  deriving DecidableEq, Repr

/-- Preflight data for one exact dyadic comparison. -/
structure CompareCost where
  lower : EndpointCost
  upper : EndpointCost
  alignmentShift : Nat
  deriving DecidableEq, Repr

namespace EndpointCost

/-- Number of binary digits needed for a natural number, with zero costing
zero digits. -/
def natBits (value : Nat) : Nat :=
  if value = 0 then 0 else value.log2 + 1

/-- Compute endpoint size without shifting its mantissa. -/
def ofDyadic : Dyadic → EndpointCost
  | .zero => ⟨0, 0, 0⟩
  | .ofOdd numerator exponent _ =>
      ⟨natBits numerator.natAbs, natBits exponent.natAbs, exponent.natAbs⟩

/-- Test `numeratorBits + exponentMagnitude ≤ maxEndpointHeight` without first
forming a potentially oversized sum. -/
def allowed (limit : EndpointLimit) (cost : EndpointCost) : Bool :=
  cost.numeratorBits ≤ limit.maxEndpointHeight &&
    cost.exponentMagnitude ≤ limit.maxEndpointHeight - cost.numeratorBits

end EndpointCost

namespace CompareCost

/-- Compute exact-comparison cost without performing the exponent-alignment
shift used by `Dyadic.blt`. -/
def ofDyadic (lower upper : Dyadic) : CompareCost :=
  let alignmentShift :=
    match lower, upper with
    | .ofOdd _ lowerExponent _, .ofOdd _ upperExponent _ =>
        (upperExponent - lowerExponent).natAbs
    | _, _ => 0
  ⟨EndpointCost.ofDyadic lower, EndpointCost.ofDyadic upper, alignmentShift⟩

/-- Decide whether an exact comparison is permitted by the configured endpoint
and alignment budgets. -/
def allowed (limit : EndpointLimit) (cost : CompareCost) : Bool :=
  cost.lower.allowed limit && cost.upper.allowed limit &&
    cost.alignmentShift ≤ limit.maxAlignmentShift

end CompareCost

namespace Raw

/-- Decide whether raw cuts describe a canonical nonempty interval.

Unbounded pairs are always consistent.  Finite endpoints are consistent when
the lower endpoint is smaller, or when the endpoints agree and both cuts are
closed.  `empty` is itself canonical. -/
def consistent : Raw → Bool
  | .empty => true
  | .bounds (.finite lower lowerStrict) (.finite upper upperStrict) =>
      if lower < upper then
        true
      else if lower = upper then
        !lowerStrict && !upperStrict
      else
        false
  | .bounds _ _ => true

/-- Propositional form of `consistent`, used by the bundled representation
candidate and by later semantic theorems. -/
def CutConsistent (raw : Raw) : Prop := raw.consistent = true

instance (raw : Raw) : Decidable raw.CutConsistent :=
  inferInstanceAs (Decidable (raw.consistent = true))

/-- Canonicalize already-preflighted raw cuts, preserving a consistent value
and mapping every inconsistent finite pair to the unique `empty`
representation.

This function may align finite dyadic endpoints. Call `normalizeWithin` at an
untrusted or planner-facing boundary. -/
def normalize (raw : Raw) : Raw :=
  if raw.consistent then raw else .empty

@[simp]
theorem consistent_empty : Raw.empty.consistent = true := rfl

@[simp]
theorem cutConsistent_empty : Raw.empty.CutConsistent := rfl

/-- Normalization always produces consistent cuts. -/
@[simp]
theorem consistent_normalize (raw : Raw) : raw.normalize.CutConsistent := by
  by_cases h : raw.consistent = true <;>
    simp [CutConsistent, normalize, h]

/-- A consistent raw value is already canonical. -/
theorem normalize_eq_self (raw : Raw) (h : raw.CutConsistent) : raw.normalize = raw := by
  simp only [CutConsistent] at h
  simp [normalize, h]

/-- An inconsistent raw value normalizes to `empty`. -/
theorem normalize_eq_empty (raw : Raw) (h : ¬raw.CutConsistent) : raw.normalize = .empty := by
  simp only [CutConsistent] at h
  simp [normalize, h]

/-- A raw value is fixed by normalization exactly when its cuts are
consistent. -/
theorem normalize_eq_self_iff (raw : Raw) : raw.normalize = raw ↔ raw.CutConsistent := by
  constructor
  · intro h
    rw [← h]
    exact consistent_normalize raw
  · exact normalize_eq_self raw

/-- Canonicalization is idempotent. -/
@[simp]
theorem normalize_idem (raw : Raw) : raw.normalize.normalize = raw.normalize :=
  normalize_eq_self _ (consistent_normalize raw)

/-- Result of resource-safe normalization. A rejected value carries the cost
that exceeded the configured endpoint or alignment limit. -/
inductive NormalizeResult where
  | ready (raw : Raw) (isConsistent : raw.CutConsistent)
  | resourceLimit (cost : CompareCost)

/-- Resource-safe normalization for untrusted raw interval data. Finite
endpoints are compared only after their exact cost passes `limit`; all other
shapes require no alignment and are immediately canonical. -/
def normalizeWithin (limit : EndpointLimit) (raw : Raw) : NormalizeResult :=
  match raw with
  | .bounds (.finite lower _) (.finite upper _) =>
      let cost := CompareCost.ofDyadic lower upper
      if cost.allowed limit then
        .ready raw.normalize (consistent_normalize raw)
      else
        .resourceLimit cost
  | _ => .ready raw.normalize (consistent_normalize raw)

end Raw

end Hex.Interval
