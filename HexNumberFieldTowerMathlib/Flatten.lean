/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Split
public import HexRowReduceMathlib

public section

/-!
# Correctness of primitive-element flattening

The executable certificate checks a tower-basis round trip and the primitive
minimal-polynomial relation. Irreducibility and the equal dimension then give
the opposite round trip and multiplicativity.
-/

namespace Hex.NumberTower

namespace Flattening

/-- Mathematical meaning of a checked primitive presentation. -/
def Sound {T : NumberTower} (F : Flattening T) : Prop :=
  letI : ZPoly.CheckedIrreducible F.root.p := F.root.checked
  Function.LeftInverse F.fromPrimitive F.toPrimitive ∧
    Function.RightInverse F.fromPrimitive F.toPrimitive ∧
    (∀ a : Elem T,
      QAdjoin.toComplex (F.toPrimitive a) F.root.rep F.root.rep_mk =
        T.toComplex a) ∧
    (∀ a : QAdjoin F.root.p F.root.x,
      T.toComplex (F.fromPrimitive a) =
        QAdjoin.toComplex a F.root.rep F.root.rep_mk) ∧
    (∀ a b : Elem T,
      F.toPrimitive (a + b) = F.toPrimitive a + F.toPrimitive b) ∧
    (∀ a b : Elem T,
      F.toPrimitive (a * b) = F.toPrimitive a * F.toPrimitive b) ∧
    ∀ a : Elem T, F.toPrimitive a⁻¹ = (F.toPrimitive a)⁻¹

end Flattening

/-- Every returned primitive presentation has inverse coordinate maps,
preserves arithmetic, and commutes with the fixed complex embeddings. -/
theorem flatten?_sound (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) :
    F.Sound := by
  sorry

/-- Exactification, primitive search, and coordinate recovery always produce
a checked primitive presentation. -/
theorem flatten?_isSome (T : NumberTower) :
    T.flatten?.isSome := by
  sorry

/-- The forward primitive coordinate map preserves the fixed complex value. -/
theorem flatten_toComplex (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) (a : Elem T) :
    QAdjoin.toComplex (F.toPrimitive a) F.root.rep F.root.rep_mk =
      T.toComplex a := by
  sorry

/-- The inverse primitive coordinate map preserves the fixed complex value. -/
theorem flatten_fromComplex (T : NumberTower) {F : Flattening T}
    (h : T.flatten? = some F) (a : QAdjoin F.root.p F.root.x) :
    T.toComplex (F.fromPrimitive a) =
      QAdjoin.toComplex a F.root.rep F.root.rep_mk := by
  sorry

end Hex.NumberTower
