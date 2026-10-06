/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseEvaluate

public section

namespace Hex.RealClosure.BaseContext

/-- A field carrier with its native arithmetic and equality dictionaries. -/
structure FieldData where
  Carrier : Type
  field : Lean.Grind.Field Carrier
  equal : DecidableEq Carrier

@[expose, reducible] def towerData : Nat → FieldData
  | 0 => ⟨Rat, inferInstance, inferInstance⟩
  | n + 1 =>
    let previous := towerData n
    letI := previous.field
    letI := previous.equal
    ⟨RationalFn previous.Carrier, inferInstance, inferInstance⟩

/-- A positional rational-function field used internally to align real
provider variables. Native context handles retain their original providers
and progress proofs; this field does not create new context handles. -/
@[expose, reducible] def BaseTower (n : Nat) : Type := (towerData n).Carrier

@[instance_reducible] instance towerField (n : Nat) : Lean.Grind.Field (BaseTower n) :=
  (towerData n).field

@[instance_reducible] instance towerEq (n : Nat) : DecidableEq (BaseTower n) :=
  (towerData n).equal

namespace BaseTower

/-- Exchange variables at adjacent positions counted from the outside.
Lifting through newer variables leaves those variables fixed. -/
def adjacent : (n i : Nat) → i + 1 < n → FieldEmbedding (BaseTower n) (BaseTower n)
  | 0, _, impossible => by omega
  | 1, _, impossible => by omega
  | n + 2, 0, _ => FieldEmbedding.swap (BaseTower n)
  | n + 2, i + 1, bound => (adjacent (n + 1) i (by omega)).rationalFunctions

/-- Two exchanges at the same position restore every stored fraction. -/
theorem adjacent_involution (n i : Nat) (bound : i + 1 < n) :
    (adjacent n i bound).comp (adjacent n i bound) = FieldEmbedding.identity (BaseTower n) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases i with
      | zero => exact FieldEmbedding.swap_involution
      | succ i =>
        change (adjacent (n + 1) i _).rationalFunctions.comp
          (adjacent (n + 1) i _).rationalFunctions = _
        rw [FieldEmbedding.rationalFunctions_comp, ih,
          FieldEmbedding.rationalFunctions_identity]

/-- Include a positional field as constants in additional outer levels. -/
def extend (n : Nat) : (extra : Nat) → FieldEmbedding (BaseTower n) (BaseTower (n + extra))
  | 0 => FieldEmbedding.identity (BaseTower n)
  | extra + 1 => (extend n extra).comp (FieldEmbedding.constants (BaseTower (n + extra)))

/-- The variable at a position counted from the outside. -/
def generator : (n i : Nat) → i < n → BaseTower n
  | 0, _, impossible => by omega
  | n + 1, 0, _ => RationalFn.X
  | n + 1, i + 1, bound => RationalFn.C (generator n i (by omega))

end BaseTower
end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.adjacent_involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.adjacent_involution
