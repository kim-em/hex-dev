/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PolyOps.Laws

public section

/-! Lawful exact adapters. Replay recomputes a finite coefficient claim using core arithmetic;
the unit certificate carries no trusted arithmetic assertion. A retract permits redundant
representatives without requiring structural equality on the representation type. -/

namespace Hex.PolyOps

universe u v

structure Representation (C : Type u) (D : Type v) where
  decode : C → D
  encode : D → C
  decode_encode : ∀ d, decode (encode d) = d

@[expose] def Representation.model (r : Representation C D) : Interpretation C D :=
  ⟨fun _ => True, r.decode⟩

@[expose] def Representation.id (D : Type u) : Representation D D := ⟨fun a => a, fun a => a, fun _ => rfl⟩

namespace Total

variable [Lean.Grind.CommRing D] [LT D] [DecidableEq D] [DecidableLT D]

instance (r : Representation C D) (c : Claim C) : Decidable (c.Holds r.model) :=
  match c with
  | .valid _ => inferInstanceAs (Decidable True)
  | .add a b c => inferInstanceAs
      (Decidable (True ∧ True ∧ True ∧ r.decode c = r.decode a + r.decode b))
  | .mul a b c => inferInstanceAs
      (Decidable (True ∧ True ∧ True ∧ r.decode c = r.decode a * r.decode b))
  | .neg a c => inferInstanceAs (Decidable (True ∧ True ∧ r.decode c = -r.decode a))
  | .zero a z => inferInstanceAs (Decidable (True ∧ (z = true ↔ r.decode a = 0)))
  | .sign a .negative => inferInstanceAs (Decidable (True ∧ r.decode a < 0))
  | .sign a .zero => inferInstanceAs (Decidable (True ∧ r.decode a = 0))
  | .sign a .positive => inferInstanceAs (Decidable (True ∧ 0 < r.decode a))
  | .inverse a c => inferInstanceAs
      (Decidable (True ∧ True ∧ r.decode a ≠ 0 ∧ r.decode a * r.decode c = 1))
  | .division a b c => inferInstanceAs
      (Decidable (True ∧ True ∧ True ∧ r.decode b ≠ 0 ∧ r.decode b * r.decode c = r.decode a))

/-- The producer allocates one unit certificate, whose wire representation is one byte.
The call itself is charged by the checked wrapper; this charge counts local arithmetic. -/
@[expose] def emit (f : Unit → α) : Computation E α := do
  charge .operations
  charge .evidenceNodes
  charge .evidenceBytes
  return f ()

@[expose] def check (r : Representation C D) (c : Claim C) (b : Budget) (_ : Unit) :
    CheckResult :=
  match b.spend .operations 1 with
  | none => .exhausted (.resource .operations) b
  | some b' =>
    match b'.spend .evidenceNodes 1 with
    | none => .exhausted (.resource .evidenceNodes) b'
    | some b'' =>
      match b''.spend .evidenceBytes 1 with
      | none => .exhausted (.resource .evidenceBytes) b''
      | some rest =>
        if c.Holds r.model then .accepted rest else .rejected (.evidence "false claim") rest

theorem check_sound (r : Representation C D) (c : Claim C) (b b' : Budget) (e : Unit)
    (h : check r c b e = .accepted b') : c.Holds r.model := by
  unfold check at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · assumption
  · contradiction

/-- A successful sign is certified by replay; order laws are required separately for
completeness of this choice on arbitrary semantic carriers. -/
@[expose] def sign [Zero D] [LT D] [DecidableLT D] [DecidableEq D] (a : D) : Sign :=
  if a < 0 then .negative else if a = 0 then .zero else .positive

@[expose] def coeffOps (r : Representation C D) (literalBytes : C → Nat) : CoeffOps C where
  Evidence := fun _ => Unit
  zero := r.encode 0
  one := r.encode 1
  check := check r
  retain a := charge .evidenceBytes (literalBytes a)
  validate _ := emit fun _ => ()
  add a b := emit fun _ => ⟨r.encode (r.decode a + r.decode b), ()⟩
  mul a b := emit fun _ => ⟨r.encode (r.decode a * r.decode b), ()⟩
  neg a := emit fun _ => ⟨r.encode (-r.decode a), ()⟩
  zeroTest a := emit fun _ => ⟨decide (r.decode a = 0), ()⟩
  sign a := emit fun _ => ⟨sign (r.decode a), ()⟩

omit [Lean.Grind.CommRing D] [LT D] [DecidableEq D] [DecidableLT D] in
theorem emit_failure (m : Interpretation C D) (inputs : List C) (f : Unit → α)
    (b : Budget) : FailureSound m inputs (emit (E := E) f b) := by
  cases h₁ : b.spend .operations 1 with
  | none => simp [emit, bind, charge, Result.bind, h₁, FailureSound]
  | some b₁ =>
    cases h₂ : b₁.spend .evidenceNodes 1 with
    | none => simp [emit, bind, charge, Result.bind, h₁, h₂, FailureSound]
    | some b₂ =>
      cases h₃ : b₂.spend .evidenceBytes 1 <;>
        simp [emit, bind, pure, charge, Result.bind, h₁, h₂, h₃, FailureSound]

theorem lawful [LE D] [Std.IsLinearOrder D] [Std.LawfulOrderLT D]
    [Lean.Grind.OrderedRing D] (r : Representation C D) (literalBytes : C → Nat) :
    CoefficientLaws (coeffOps r literalBytes) r.model where
  valid_zero := trivial
  valid_one := trivial
  denote_zero := r.decode_encode 0
  denote_one := r.decode_encode 1
  check_sound := fun c b e b' h => check_sound r c b b' e h
  retain_failure := by
    intro a b
    change FailureSound r.model [a] (charge .evidenceBytes (literalBytes a) b)
    unfold charge
    split <;> trivial
  validate_failure := by
    intro a b
    change FailureSound r.model [a] (emit (fun _ => ()) b)
    exact emit_failure ..
  add_failure := fun _ _ _ => emit_failure ..
  mul_failure := fun _ _ _ => emit_failure ..
  neg_failure := fun _ _ => emit_failure ..
  zero_failure := fun _ _ => emit_failure ..
  sign_failure := fun _ _ => emit_failure ..

end Total

/-- Logical literal size: one sign byte and a base-128 variable-length magnitude. -/
@[expose] def intBytes (n : Int) : Nat := n.natAbs.log2 / 7 + 2

/-- A rational literal stores its signed numerator and positive denominator payload. -/
@[expose] def ratBytes (q : Rat) : Nat := intBytes q.num + q.den.log2 / 7 + 1

/-- Exact integer coefficients, with no field instance. -/
@[expose] def intOps : CoeffOps Int := Total.coeffOps (.id Int) intBytes

/-- Exact rational coefficients. -/
@[expose] def ratOps : FieldOps Rat where
  toCoeffOps := Total.coeffOps (.id Rat) ratBytes
  inv a := Total.emit fun _ => ⟨a⁻¹, ()⟩

/-- Integer exact division proposes a quotient only after the divisibility test succeeds. -/
@[expose] def intExactOps : ExactOps Int where
  toCoeffOps := intOps
  divExact a b := do
    charge .operations
    if b = 0 then
      fun rest => .exhausted (.unavailable "nonzero divisor required") rest
    else if a % b = 0 then Total.emit fun _ => ⟨a / b, ()⟩
    else fun rest => .exhausted (.unavailable "exact quotient unavailable") rest

/-- Rational exact quotients use the same finite claim checker as inversion. -/
@[expose] def ratExactOps : ExactOps Rat where
  toCoeffOps := ratOps.toCoeffOps
  divExact a b := Total.emit fun _ => ⟨a / b, ()⟩

theorem intOps_lawful : CoefficientLaws intOps (Representation.id Int).model := Total.lawful _ _
theorem ratOps_lawful : CoefficientLaws ratOps.toCoeffOps (Representation.id Rat).model := Total.lawful _ _

theorem ratOps_fieldLaws : FieldLaws ratOps (Representation.id Rat).model where
  toCoefficientLaws := ratOps_lawful
  inv_failure := fun _ _ => Total.emit_failure ..

theorem ratExactOps_lawful : ExactLaws ratExactOps (Representation.id Rat).model where
  toCoefficientLaws := ratOps_lawful
  division_failure := fun _ _ _ => Total.emit_failure ..

theorem intExactOps_lawful : ExactLaws intExactOps (Representation.id Int).model where
  toCoefficientLaws := intOps_lawful
  division_failure := by
    intro a c b
    cases h : b.spend .operations 1 with
    | none => simp [intExactOps, bind, charge, Result.bind, h, FailureSound]
    | some rest =>
      simp only [intExactOps, bind, charge, h, Result.bind]
      split
      · trivial
      · split
        · exact Total.emit_failure ..
        · trivial

end Hex.PolyOps
