/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Precision.Inputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofProbe.Precision.Inputs
public meta import HexRCF.ProofProbe.Literals.Support
@[expose] public section

namespace Hex.RCF.ProofProbe.Precision.Full64
open Hex RealCoefficients
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option Elab.async false
set_option debug.skipKernelTC false
set_option rcf.algebraic.reducedLiterals false
set_option rcf.algebraic.intervalSigns true
set_option rcf.algebraic.singleReplay false
set_option rcf.algebraic.indexSigns true
set_option rcf.algebraic.monicCore true
set_option rcf.algebraic.signRefinements 0

-- Each fresh arm checks its own constructor and selected-root transport.
abbrev square : DyadicSquare :=
  ⟨Dyadic.ofInt 13043817825332782212 >>> (63 : Int), 0, 64⟩
abbrev hw : atomWitness SquareTwo.polynomial square := by decide +kernel
abbrev hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ square.prec := by decide +kernel
abbrev root := SimpleRoot.ofSquare SquareTwo.polynomial square hw hp
def values : Fin 1 → PolyQuot SquareTwo.polynomial root :=
  fun _ => SquareTwo.coordinate square hw hp

theorem selected :
    Field.value (Field.literalRep SquareTwo.polynomial square hw hp) (values 0) =
      Real.sqrt 2 := by
  apply SquareTwo.value square hw hp (by decide +kernel)
  have positive : square.radiusHi < square.re := by decide +kernel
  have rational := Dyadic.toRat_lt_toRat_iff.mpr positive
  rw [Dyadic.toRat_sub]
  exact_mod_cast sub_pos.mpr rational

abbrev ownSentence : Prop := ∃ x : ℝ, GeneratorWindowTests.matrix.toProp
  (RealFormula.append (fun j => Field.value
    (Field.literalRep SquareTwo.polynomial square hw hp) (values j)) x)

theorem sameSentence : ownSentence ↔ sentence8 := by
  have same : (fun j : Fin 1 => Field.value
      (Field.literalRep SquareTwo.polynomial square hw hp) (values j)) =
      (fun j : Fin 1 => Field.value (Field.literalRep SquareTwo.polynomial SquareTwo.square
        GeneratorWindowTests.hw GeneratorWindowTests.hp) (GeneratorWindowTests.values j)) := by
    funext j
    have equal : j = 0 := Subsingleton.elim _ _
    subst j
    exact selected.trans selected8.symm
  dsimp only [ownSentence, sentence8]
  rw [same]

elab "precision_build64" : tactic => Lean.Elab.Tactic.liftMetaTactic fun goal => do
  let s ← FieldRuntime.evalSquare (Lean.mkConst ``square)
  if hw : atomWitness SquareTwo.polynomial s then
    if hp : (mahlerPrec SquareTwo.polynomial : Int) ≤ s.prec then
      let runtimeValues : Fin 1 → PolyQuot SquareTwo.polynomial
          (SimpleRoot.ofSquare SquareTwo.polynomial s hw hp) :=
        fun _ => SquareTwo.coordinate s hw hp
      let (proof, _, _, _) ← FieldLiteral.proveRefiningWithCertificate
        (Lean.mkConst ``SquareTwo.polynomial) (Lean.mkConst ``root)
        (Lean.mkConst ``values) (Lean.mkConst ``GeneratorWindowTests.matrix)
        runtimeValues GeneratorWindowTests.matrix .existsReal
      let proof ← Lean.Meta.mkAppM ``Iff.mp #[Lean.mkConst ``sameSentence, proof]
      let proof ← Hex.RCF.checkProof `Hex.RCF.ProofProbe.Precision.Full64
        (← goal.getType) proof
      goal.assign proof
      return []
    else throwError "insufficient initial precision"
  else throwError "invalid initial square"

theorem witness : sentence8 := by precision_build64

#print axioms witness
end Hex.RCF.ProofProbe.Precision.Full64
