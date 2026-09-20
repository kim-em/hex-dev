/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPoly.PolyOps.Coeff

public section

/-! Coefficient interpretation and checker soundness, without injectivity or decidability
of semantic equality. Algebraic and order assumptions belong to the semantic carrier. -/

namespace Hex.PolyOps

universe u v w

structure Interpretation (C : Type u) (D : Type w) where
  valid : C → Prop
  denote : C → D

@[expose] def Sign.Holds [Zero D] [LT D] (s : Sign) (a : D) : Prop :=
  match s with
  | .negative => a < 0
  | .zero => a = 0
  | .positive => 0 < a

/-- Validity is part of every claim, including negative zero decisions. -/
@[expose] def Claim.Holds [Zero D] [One D] [Add D] [Mul D] [Neg D] [LT D]
    (m : Interpretation C D) : Claim C → Prop
  | .valid a => m.valid a
  | .add a b c => m.valid a ∧ m.valid b ∧ m.valid c ∧ m.denote c = m.denote a + m.denote b
  | .mul a b c => m.valid a ∧ m.valid b ∧ m.valid c ∧ m.denote c = m.denote a * m.denote b
  | .neg a c => m.valid a ∧ m.valid c ∧ m.denote c = -m.denote a
  | .zero a z => m.valid a ∧ (z = true ↔ m.denote a = 0)
  | .sign a s => m.valid a ∧ s.Holds (m.denote a)
  | .inverse a c => m.valid a ∧ m.valid c ∧ m.denote a ≠ 0 ∧ m.denote a * m.denote c = 1
  | .division a b c => m.valid a ∧ m.valid b ∧ m.valid c ∧
      m.denote b ≠ 0 ∧ m.denote b * m.denote c = m.denote a

/-- A ring callback may report invalid input only for an invalid operand. Mathematical
zero-divisor errors belong to guarded inversion/division, not to total ring operations. -/
@[expose] def FailureSound (m : Interpretation C D) (inputs : List C) (r : Result α E) : Prop :=
  match r with
  | .invalid _ _ => ∃ a ∈ inputs, ¬ m.valid a
  | _ => True

/-- Soundness alone asserts no eventual success. In particular a checker that always
exhausts does not acquire a completeness theorem from this law package. -/
structure CoefficientLaws [Lean.Grind.CommRing D] [LE D] [LT D]
    [Std.IsLinearOrder D] [Std.LawfulOrderLT D] [Lean.Grind.OrderedRing D]
    (ops : CoeffOps C) (m : Interpretation C D) : Prop where
  valid_zero : m.valid ops.zero
  valid_one : m.valid ops.one
  denote_zero : m.denote ops.zero = 0
  denote_one : m.denote ops.one = 1
  check_sound : ∀ claim b e b', ops.check claim b e = .accepted b' → claim.Holds m
  retain_failure : ∀ a b, FailureSound m [a] (ops.retain a b)
  validate_failure : ∀ a b, FailureSound m [a] (ops.validate a b)
  add_failure : ∀ a c b, FailureSound m [a, c] (ops.add a c b)
  mul_failure : ∀ a c b, FailureSound m [a, c] (ops.mul a c b)
  neg_failure : ∀ a b, FailureSound m [a] (ops.neg a b)
  zero_failure : ∀ a b, FailureSound m [a] (ops.zeroTest a b)
  sign_failure : ∀ a b, FailureSound m [a] (ops.sign a b)

/-- Independent accepted zero and sign decisions agree. -/
theorem CoefficientLaws.sign_zero [Lean.Grind.CommRing D] [LE D] [LT D]
    [Std.IsLinearOrder D] [Std.LawfulOrderLT D] [Lean.Grind.OrderedRing D]
    {ops : CoeffOps C} {m : Interpretation C D} (laws : CoefficientLaws ops m)
    (a : C) (z : Bool) (s : Sign) (ez : ops.Evidence (.zero a z))
    (es : ops.Evidence (.sign a s)) {b₁ b₂ b₃ b₄ : Budget}
    (hz : ops.check (.zero a z) b₁ ez = .accepted b₂)
    (hs : ops.check (.sign a s) b₃ es = .accepted b₄) :
    z = true ↔ s = .zero := by
  have hz := laws.check_sound _ _ _ _ hz
  have hs := laws.check_sound _ _ _ _ hs
  cases s <;> simp only [Claim.Holds, Sign.Holds] at hz hs <;> grind

/-- Uniform envelopes are cofinal in the finite shared counter set. This is a progress
contract, separate from semantic soundness. -/
def Eventually (f : Computation E α) : Prop :=
  ∃ n, ∀ b, (Limits.uniform n).budget.Within b → (f b).isSome = true

structure OperationProgress (ops : CoeffOps C) (m : Interpretation C D) : Prop where
  retain : ∀ a, m.valid a → Eventually (ops.retainWith a)
  validate : ∀ a, m.valid a → Eventually (ops.validateWith a)
  add : ∀ a b, m.valid a → m.valid b → Eventually (ops.addWith a b)
  mul : ∀ a b, m.valid a → m.valid b → Eventually (ops.mulWith a b)
  neg : ∀ a, m.valid a → Eventually (ops.negWith a)
  zeroTest : ∀ a, m.valid a → Eventually (ops.zeroWith a)
  sign : ∀ a, m.valid a → Eventually (ops.signWith a)

/-- A backend supplies a computable sufficient replay envelope for each literal certificate.
The bound governs replay of retained evidence, not a fresh coefficient search. -/
structure ReplayBound (ops : CoeffOps C) where
  allowance : (claim : Claim C) → ops.Evidence claim → Nat

/-- Already accepted evidence remains replayable with the backend's sufficient resources.
This is separate from both checker soundness and operation progress. -/
structure ReplayLaws (ops : CoeffOps C) (bounds : ReplayBound ops) : Prop where
  replay : ∀ claim e initial final, ops.check claim initial e = .accepted final →
    ∀ b, (Limits.uniform (bounds.allowance claim e)).budget.Within b →
      (ops.checkWith claim e b).isSome = true

/-- Field interpretations add the core field laws on the semantic carrier; no such instance
is installed on raw representatives. -/
structure FieldLaws [Lean.Grind.Field D] [LE D] [LT D]
    [Std.IsLinearOrder D] [Std.LawfulOrderLT D] [Lean.Grind.OrderedRing D]
    (ops : FieldOps C) (m : Interpretation C D)
    : Prop extends CoefficientLaws ops.toCoeffOps m where
  inv_failure : ∀ a b, FailureSound m [a] (ops.inv a b)

structure ExactLaws [Lean.Grind.CommRing D] [LE D] [LT D]
    [Std.IsLinearOrder D] [Std.LawfulOrderLT D] [Lean.Grind.OrderedRing D]
    (ops : ExactOps C) (m : Interpretation C D)
    : Prop extends CoefficientLaws ops.toCoeffOps m where
  division_failure : ∀ a c b, FailureSound m [a, c] (ops.divExact a c b)

/-- Acceptance of the bounded wrapper implies acceptance by the backend checker. -/
theorem CoeffOps.checkWith_accepted (ops : CoeffOps C) (c : Claim C) (e : ops.Evidence c)
    {b b' : Budget} (h : ops.checkWith c e b = .ok () b') :
    ∃ start finish, ops.check c start e = .accepted finish := by
  obtain ⟨_, _, _, h⟩ := Result.bind_ok h
  obtain ⟨start, h⟩ := invoke_ok h
  cases hc : ops.check c start e with
  | accepted finish => exact ⟨start, finish, hc⟩
  | rejected => simp [hc, CheckResult.result] at h
  | exhausted => simp [hc, CheckResult.result] at h

/-- Polynomial identities compare every interpreted coefficient, defaulting to semantic
zero outside storage. No equality or algebraic instances on representatives are involved. -/
@[expose] def coefficient [Zero D] (m : Interpretation C D) (p : Array C) (i : Nat) : D :=
  match p[i]? with
  | some c => m.denote c
  | none => 0

@[expose] def PolyEq [Zero D] (m : Interpretation C D) (p q : Array C) : Prop :=
  ∀ i, coefficient m p i = coefficient m q i

@[expose] def HasDegree [Zero D] (m : Interpretation C D) (p : Array C) : Option Nat → Prop
  | none => ∀ i, coefficient m p i = 0
  | some d => coefficient m p d ≠ 0 ∧ ∀ i, d < i → coefficient m p i = 0

end Hex.PolyOps
