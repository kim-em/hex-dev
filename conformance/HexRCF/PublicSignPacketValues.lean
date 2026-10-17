/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.PublicSignPacket
public import HexRCF.RealCoefficients.ScalarQuote
public meta import HexRCF.PublicSignPacket
public meta import HexRCF.RealCoefficients.ScalarQuote
public meta import HexRCF.RealCoefficients.RationalQuote

public section

/-! Decode a coefficient using only the public packet's checked sign fact,
then interpret that exact coefficient at the original selected real root. -/

open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.PublicSignPacket

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

@[expose] def literal : Codec.Json := .array (.cons polynomial (.cons (.number 1) .nil))

run_meta do
  let codec : Q(ValueCodec (Algebraic.Element context)) :=
    q(Algebraic.Element.codec (context := context) RootQuoteTests.base.codec)
  let facts ← mkAppM ``List.cons #[mkConst ``fact,
    ← mkAppOptM ``List.nil #[some (← inferType (mkConst ``fact))]]
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
  let .ok quoted ← RootQuote.runWith
      (ScalarQuote.quoteWith codec facts (mkConst ``literal) decode)
    | throwError "public packet did not decode its coefficient"
  let declaration := Declaration.defnDecl {
    name := `Hex.RCF.PublicSignPacket.coefficient,levelParams := [],
    type := ← inferType quoted.value,value := quoted.value,hints := .regular 0,safety := .safe}
  addDecl declaration (forceExpose := true)
  compileDecl declaration (logErrors := true)
  let reader := mkApp3 (mkConst ``ValueCodec.decode) (← inferType quoted.value) codec
    (mkConst ``literal)
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[mkConst `Hex.RCF.PublicSignPacket.coefficient])
  let proof ← Hex.RCF.checkProof `publicPacketCoefficient statement quoted.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.PublicSignPacket.coefficient_read,levelParams := [],type := statement,value := proof})
  logInfo m!"coefficient from public packet; proofNodes={quoted.usage.proofNodes}"

theorem coefficient_polynomial : coefficient.polynomial =
    DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(1 : Rat)⟩] : Array RootQuoteTests.base.Value) := by
  unfold coefficient
  rw [Algebraic.Element.restore_polynomial]
  exact (DensePoly.ofCoeffs_toArray _).symm

theorem coefficient_sign : coefficient.sign = 1 := by
  unfold coefficient
  exact Algebraic.Element.restore_sign _ _ _ _

@[expose] noncomputable def coefficientReal : ℝ :=
  coefficient.denote model.value model.zero_iff model.one model.add model.sub model.mul
    model.nat model.sign

private theorem polynomial_value :
    HexPolyTheory.Interpret.interpret model.value model.zero_iff
      (DensePoly.ofCoeffs (#[⟨(0 : Rat)⟩,⟨(1 : Rat)⟩] : Array RootQuoteTests.base.Value)) =
        (Polynomial.X : Polynomial ℝ) := by
  ext i
  rw [HexPolyTheory.Interpret.coeff_interpret]
  rcases i with _ | _ | i
  · change RootQuoteTests.realModel.value (⟨(0 : Rat)⟩ : RootQuoteTests.base.Value) = _
    erw [RootQuoteTests.rational_value]
    norm_num
  · change RootQuoteTests.realModel.value (⟨(1 : Rat)⟩ : RootQuoteTests.base.Value) = _
    erw [RootQuoteTests.rational_value]
    norm_num
  · rw [DensePoly.coeff_eq_zero_of_size_le _ (by change 2 ≤ i+1+1; omega)]
    have zero := (model.zero_iff 0).mpr rfl
    erw [zero]
    rw [Polynomial.coeff_X, ite_eq_right (by omega : ¬1 = i+1+1)]

theorem coefficient_value : coefficientReal = RootQuoteTests.realRoot := by
  unfold coefficientReal Algebraic.Element.denote
  rw [coefficient_polynomial]
  unfold Algebraic.Context.evalPoly
  rw [polynomial_value, Polynomial.eval_X]
  simp only [Algebraic.Context.rootValue, context, Algebraic.Context.root_adjoin]
  rfl

theorem coefficient_positive : 0 < coefficientReal := by
  have signed := Algebraic.Element.sign_spec model.value model.zero_iff model.one
    model.add model.sub model.mul model.nat model.sign model.neg model.inv coefficient
  rw [coefficient_sign] at signed
  apply sign_eq_one_iff.mp
  change 1 = (SignType.sign coefficientReal : Int) at signed
  cases chosen : SignType.sign coefficientReal <;> simp_all

end Hex.RCF.PublicSignPacket
