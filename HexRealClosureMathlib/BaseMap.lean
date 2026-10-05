/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseRealization

public section

namespace Hex.RealClosure.BaseContext

variable {K : Type} [Lean.Grind.Field K] [DecidableEq K]

/-- Interpret a checked native coefficient map as a field hom, retaining its
actual cached value function and both native dictionaries. -/
@[expose] noncomputable def FieldEmbedding.hom {L : Type}
    [Lean.Grind.Field L] [DecidableEq L] (map : FieldEmbedding K L) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI : Field L := HexPolyMathlib.fieldOfGrind
    K →+* L := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field L := HexPolyMathlib.fieldOfGrind
  exact
    { toFun := map.value
      map_zero' := (map.zero 0).mpr rfl
      map_one' := map.one
      map_add' := map.add
      map_mul' := map.mul }

/-- The field hom uses exactly the native inclusion closure. -/
theorem FieldEmbedding.hom_apply {L : Type} [Lean.Grind.Field L] [DecidableEq L]
    (map : FieldEmbedding K L) (a : K) : map.hom a = map.value a := rfl

end Hex.RealClosure.BaseContext
