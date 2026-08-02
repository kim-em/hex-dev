/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.Coordinates

public section

/-!
# Total primitive presentations

Assembly and semantic invariants for the common-field presentation of an
array of canonical algebraic numbers.
-/

namespace Hex.AlgebraicPoly.Common

/-- A nonzero algebraic coefficient array always admits a checked primitive
fixed-field presentation. -/
theorem presentation?_isSome (coefficients : Array AlgebraicNumber)
    (hnonzero : ∃ a ∈ coefficients.toList, a.isZero = false) :
    (presentation? coefficients).isSome := by
  obtain ⟨gamma, hgamma⟩ := Option.isSome_iff_exists.mp
    (primitive?_isSome coefficients hnonzero)
  obtain ⟨powers, hpowers⟩ := Option.isSome_iff_exists.mp
    (powers?_isSome gamma (2 * degree gamma - 2))
  obtain ⟨hpowersSize, hpowersValues⟩ :=
    powers?_sound gamma (2 * degree gamma - 2) hpowers
  have hsize : powers.size = 2 * degree gamma - 1 := by
    have hpos := degree_pos gamma
    omega
  have hembeddedSome :
      (coefficients.mapM fun a => coordinates? gamma a powers).isSome := by
    apply HexRootsMathlib.array_mapM_isSome
    intro a ha
    apply coordinates?_isSome gamma a powers hsize hpowersValues
    exact primitive?_contains coefficients gamma a hgamma
      (Array.mem_toList_iff.mp ha)
  obtain ⟨embedded, hembedded⟩ :=
    Option.isSome_iff_exists.mp hembeddedSome
  unfold presentation?
  simp [hgamma, hpowers, hembedded]

/-- A successful presentation preserves the coefficient array length and the
selected complex value of every coefficient. -/
theorem presentation?_sound (coefficients : Array AlgebraicNumber)
    {presentation : Presentation}
    (h : presentation? coefficients = some presentation) :
    presentation.coefficients.size = coefficients.size ∧
      ∀ i (hi : i < coefficients.size)
          (hiPresentation : i < presentation.coefficients.size),
        QAdjoin.toComplex presentation.coefficients[i]
            presentation.generator.rep presentation.generator.rep_mk =
          coefficients[i].toComplex := by
  unfold presentation? at h
  obtain ⟨gamma, hgamma, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨powers, hpowers, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨embedded, hembedded, h⟩ := Option.bind_eq_some_iff.mp h
  have hpresentation : (Presentation.mk gamma embedded) = presentation :=
    Option.some.inj h
  subst presentation
  have hmap := HexRootsMathlib.array_mapM_some_get hembedded
  constructor
  · exact hmap.1.symm
  · intro i hi hiEmbedded
    exact coordinates?_sound gamma coefficients[i] powers
      (hmap.2 i hi hiEmbedded)

end Hex.AlgebraicPoly.Common
