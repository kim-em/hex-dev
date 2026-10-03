/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.GeneratorWindowInputs
@[expose] public section

namespace Hex.RCF.ProofProbe.Precision
open Hex RealCoefficients

abbrev square64 : DyadicSquare :=
  ⟨Dyadic.ofInt 13043817825332782212 >>> (63 : Int), 0, 64⟩
abbrev hw64 : atomWitness SquareTwo.polynomial square64 := by decide +kernel
abbrev hp64 : (mahlerPrec SquareTwo.polynomial : Int) ≤ square64.prec := by decide +kernel
abbrev root64 := SimpleRoot.ofSquare SquareTwo.polynomial square64 hw64 hp64
def values64 : Fin 1 → PolyQuot SquareTwo.polynomial root64 :=
  fun _ => SquareTwo.coordinate square64 hw64 hp64

theorem selected64 :
    Field.value (Field.literalRep SquareTwo.polynomial square64 hw64 hp64) (values64 0) =
      Real.sqrt 2 := by
  apply SquareTwo.value square64 hw64 hp64 (by decide +kernel)
  have positive : square64.radiusHi < square64.re := by decide +kernel
  have rational := Dyadic.toRat_lt_toRat_iff.mpr positive
  rw [Dyadic.toRat_sub]
  exact_mod_cast sub_pos.mpr rational

theorem selected8 :
    Field.value (Field.literalRep SquareTwo.polynomial SquareTwo.square
      GeneratorWindowTests.hw GeneratorWindowTests.hp) (GeneratorWindowTests.values 0) =
      Real.sqrt 2 := by
  exact (SquareTwo.coordinate_root _ _ _).trans SquareTwo.square_selected_root

abbrev sentence64 : Prop := ∃ x : ℝ, GeneratorWindowTests.matrix.toProp
  (RealFormula.append (fun j => Field.value
    (Field.literalRep SquareTwo.polynomial square64 hw64 hp64) (values64 j)) x)

abbrev sentence8 : Prop := ∃ x : ℝ, GeneratorWindowTests.matrix.toProp
  (RealFormula.append (fun j => Field.value
    (Field.literalRep SquareTwo.polynomial SquareTwo.square
      GeneratorWindowTests.hw GeneratorWindowTests.hp) (GeneratorWindowTests.values j)) x)

/-- Both fixed presentations retain the same positive embedding and formula. -/
theorem sameSentence : sentence64 ↔ sentence8 := by
  have same : (fun j : Fin 1 => Field.value
      (Field.literalRep SquareTwo.polynomial square64 hw64 hp64) (values64 j)) =
      (fun j : Fin 1 => Field.value (Field.literalRep SquareTwo.polynomial SquareTwo.square
        GeneratorWindowTests.hw GeneratorWindowTests.hp) (GeneratorWindowTests.values j)) := by
    funext j
    have equal : j = 0 := Subsingleton.elim _ _
    subst j
    exact selected64.trans selected8.symm
  dsimp only [sentence64, sentence8]
  rw [same]

end Hex.RCF.ProofProbe.Precision

/-- info: 'Hex.RCF.ProofProbe.Precision.sameSentence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.ProofProbe.Precision.sameSentence
