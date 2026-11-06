/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Field
public import HexNumberFieldTheory.CommonField
public import HexNumberFieldTheory.Primitive
public import HexRCF.RealCoefficients.CommonPresentation
public import HexRCF.RealCoefficients.FieldBuildProgress
public section

namespace Hex.RCF.RealCoefficients.Field

private theorem shift_real (theta alpha gamma : AlgebraicNumber) (c : Int)
    (thetaReal : theta.isReal = true) (alphaReal : alpha.isReal = true)
    (produced : AlgebraicPoly.Common.shift? theta alpha c = some gamma) :
    gamma.isReal = true := by
  apply (AlgebraicNumber.isReal_iff gamma).mpr
  have thetaZero : theta.toComplex.im = 0 :=
    (AlgebraicNumber.isReal_iff theta).mp thetaReal
  have alphaZero : alpha.toComplex.im = 0 :=
    (AlgebraicNumber.isReal_iff alpha).mp alphaReal
  rw [AlgebraicPoly.Common.shift?_sound theta alpha c produced]
  simp [Complex.add_im, Complex.mul_im, thetaZero, alphaZero]

private theorem extend_real (theta alpha gamma : AlgebraicNumber)
    (thetaReal : theta.isReal = true) (alphaReal : alpha.isReal = true)
    (produced : AlgebraicPoly.Common.extend? theta alpha = some gamma) :
    gamma.isReal = true := by
  cases selected : AlgebraicPoly.Common.extendShift? theta alpha with
  | none => simp [AlgebraicPoly.Common.extend?, selected] at produced
  | some shifted =>
    have same : shifted.value = gamma := by
      simpa [AlgebraicPoly.Common.extend?, selected] using produced
    apply shift_real theta alpha gamma shifted.shift thetaReal alphaReal
    simpa [same] using
      AlgebraicPoly.Common.extendShift?_source theta alpha shifted selected

private theorem fold_real (items : List AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true) (initial out : AlgebraicNumber)
    (initialReal : initial.isReal = true)
    (produced : items.foldlM AlgebraicPoly.Common.extend? initial = some out) :
    out.isReal = true := by
  induction items generalizing initial with
  | nil =>
    have same := Option.some.inj produced
    subst out
    exact initialReal
  | cons a items ih =>
    rw [List.foldlM_cons] at produced
    obtain ⟨next, built, tail⟩ := Option.bind_eq_some_iff.mp produced
    exact ih (fun b member => allReal b (by simp [member])) next
      (extend_real initial a next initialReal (allReal a (by simp)) built) tail

private theorem first_real (items : Array AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true) (first : AlgebraicNumber)
    (selected : (items.filter fun a => !a.isZero)[0]? = some first) :
    first.isReal = true := by
  obtain ⟨bound, same⟩ := Array.getElem?_eq_some_iff.mp selected
  have member : first ∈ items.filter (fun a => !a.isZero) := by
    rw [← same]
    exact Array.getElem_mem bound
  exact allReal first (Array.mem_filter.mp member).1

private theorem primitive_real (items : Array AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true) (generator : AlgebraicNumber)
    (produced : AlgebraicPoly.Common.primitive? items = some generator) :
    generator.isReal = true := by
  let nonzero := items.filter fun a => !a.isZero
  unfold AlgebraicPoly.Common.primitive? at produced
  change (nonzero[0]? >>= fun first =>
    nonzero.toList.drop 1 |>.foldlM AlgebraicPoly.Common.extend? first) = some generator at produced
  obtain ⟨first, selected, folded⟩ := Option.bind_eq_some_iff.mp produced
  apply fold_real (nonzero.toList.drop 1) _ first generator
    (first_real items allReal first selected) folded
  intro a member
  have arrayMember : a ∈ nonzero :=
    Array.mem_toList_iff.mp (List.mem_of_mem_drop member)
  exact allReal a (Array.mem_filter.mp arrayMember).1

private theorem presentationAt_real (generator : AlgebraicNumber)
    (items : Array AlgebraicNumber) (presentation : AlgebraicPoly.Common.Presentation)
    (generatorReal : generator.isReal = true)
    (produced : AlgebraicPoly.Common.presentationAt? generator items = some presentation) :
    presentation.generator.isReal = true := by
  unfold AlgebraicPoly.Common.presentationAt? at produced
  obtain ⟨powers, _, rest⟩ := Option.bind_eq_some_iff.mp produced
  obtain ⟨entries, _, result⟩ := Option.bind_eq_some_iff.mp rest
  have same := Option.some.inj result
  rw [← same]
  exact generatorReal

private theorem presentation_real (items : Array AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true)
    (presentation : AlgebraicPoly.Common.Presentation)
    (produced : AlgebraicPoly.Common.presentation? items = some presentation) :
    presentation.generator.isReal = true := by
  let proposed : Option AlgebraicPoly.Common.Presentation := do
    let first ← (items.filter fun a => !a.isZero)[0]?
    if items.all (fun a => AlgebraicPoly.Common.degree first % AlgebraicPoly.Common.degree a == 0) then
      AlgebraicPoly.Common.presentationAt? first items
    else none
  unfold AlgebraicPoly.Common.presentation? at produced
  change (match proposed with
    | some result => some result
    | none => do
      let generator ← AlgebraicPoly.Common.primitive? items
      AlgebraicPoly.Common.presentationAt? generator items) = some presentation at produced
  have proposedReal (candidate : AlgebraicPoly.Common.Presentation)
      (built : proposed = some candidate) : candidate.generator.isReal = true := by
    dsimp only [proposed] at built
    obtain ⟨first, selected, checked⟩ := Option.bind_eq_some_iff.mp built
    split at checked
    · exact presentationAt_real first items candidate
        (first_real items allReal first selected) checked
    · cases checked
  cases attempted : proposed with
  | some candidate =>
    have same : candidate = presentation := by simpa only [attempted, Option.some.injEq] using produced
    rw [← same]
    exact proposedReal candidate attempted
  | none =>
    simp only [attempted] at produced
    obtain ⟨generator, built, checked⟩ := Option.bind_eq_some_iff.mp produced
    exact presentationAt_real generator items presentation
      (primitive_real items allReal generator built) checked

private theorem fastPair_real (theta alpha : AlgebraicNumber)
    (thetaReal : theta.isReal = true) (alphaReal : alpha.isReal = true)
    (presentation : QAdjoin.Presentation)
    (produced : QAdjoin.fastPair? theta alpha = some presentation) :
    presentation.generator.isReal = true := by
  unfold QAdjoin.fastPair? at produced
  obtain ⟨gamma, shifted, rest⟩ := Option.bind_eq_some_iff.mp produced
  split at rest
  · unfold QAdjoin.presentShift? at rest
    obtain ⟨coordinates, _, result⟩ := Option.bind_eq_some_iff.mp rest
    have same := Option.some.inj result
    rw [← same]
    exact shift_real theta alpha gamma 1 thetaReal alphaReal shifted
  · cases rest

private theorem fallback_real (items : Array AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true)
    (nonzero : items.all (fun a => a.isZero) ≠ true) :
    (QAdjoin.commonFallback items).generator.isReal = true := by
  have somePresentation : (AlgebraicPoly.Common.presentation? items).isSome = true := by
    apply AlgebraicPoly.Common.presentation?_isSome
    have hn : ¬ ∀ a ∈ items, a.isZero = true :=
      fun hall => nonzero (Array.all_eq_true'.mpr hall)
    push Not at hn
    obtain ⟨a, member, hn⟩ := hn
    exact ⟨a, Array.mem_toList_iff.mpr member, Bool.eq_false_iff.mpr hn⟩
  obtain ⟨presentation, built⟩ := Option.isSome_iff_exists.mp somePresentation
  unfold QAdjoin.commonFallback
  rw [built]
  exact presentation_real items allReal presentation built

private theorem common_real_of (items : Array AlgebraicNumber)
    (allReal : ∀ a ∈ items, a.isReal = true) :
    (QAdjoin.common items).generator.isReal = true := by
  by_cases allZero : items.all (fun a => a.isZero) = true
  · unfold QAdjoin.common
    rw [ite_eq_left allZero]
    apply (AlgebraicNumber.isReal_iff 0).mpr
    simp
  · by_cases two : items.size = 2
    · cases attempted : QAdjoin.fastPair? items[0]! items[1]! with
      | none =>
        unfold QAdjoin.common
        rw [ite_eq_right allZero, ite_eq_left two, attempted]
        exact fallback_real items allReal allZero
      | some presentation =>
        unfold QAdjoin.common
        rw [ite_eq_right allZero, ite_eq_left two, attempted]
        apply fastPair_real items[0]! items[1]! _ _ presentation attempted
        · rw [getElem!_pos items 0 (by omega)]
          exact allReal _ (Array.getElem_mem (by omega))
        · rw [getElem!_pos items 1 (by omega)]
          exact allReal _ (Array.getElem_mem (by omega))
    · unfold QAdjoin.common
      rw [ite_eq_right allZero, ite_eq_right two]
      exact fallback_real items allReal allZero

/-- The actual common-field construction keeps a real selected generator when
all source coefficients are real. No extra check is required from the caller. -/
theorem common_real (bs : Array RealAlgebraicNumber) :
    (QAdjoin.common (bs.map RealAlgebraicNumber.toAlgebraic)).generator.isReal = true := by
  apply common_real_of
  intro a member
  obtain ⟨b, _, rfl⟩ := Array.mem_map.mp member
  exact b.property

/-- The produced coordinates interpret as the original real coefficients,
without a separate premise about the common generator's reality. This is a
construction law; frozen source replay checks its own literal presentation. -/
theorem common_eval (bs : Array RealAlgebraicNumber) (i : Nat) (hi : i < bs.size) :
    value (QAdjoin.common (bs.map RealAlgebraicNumber.toAlgebraic)).generator.rep
        ((QAdjoin.common (bs.map RealAlgebraicNumber.toAlgebraic)).entries[i]'(by simp [hi])) =
      bs[i].toReal :=
  common_value bs (common_real bs) i hi

end Hex.RCF.RealCoefficients.Field

namespace Hex.RCF.RealCoefficients.CommonPresentation

variable {p : ZPoly} {s : DyadicSquare}
variable {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
variable [ZPoly.CheckedIrreducible p]
local notation "E" => PolyQuot p (SimpleRoot.ofSquare p s hw hp)

/-- At a checked real field, an actual source equation passes the executable
coordinate equality test. This is a construction law, not a replay premise. -/
theorem checkEquation_complete (real : s.meetsRealAxis = true)
    (sourcePolynomial : DensePoly Rat) (coordinate : E)
    (equation : (LiteralSign.realPoly sourcePolynomial).IsRoot
      (Field.value (Field.literalRep p s hw hp) coordinate)) :
    checkEquation sourcePolynomial coordinate = true := by
  apply decide_eq_true_eq.mpr
  apply (Field.value_eq_zero (Field.literalRep p s hw hp)
    (Field.literalRep_mk p s hw hp) (Field.literalRep_real p s hw hp real) _).mp
  rw [evalAt_realPoly hw hp real]
  exact equation

/-- The actual sign-table builder authenticates all selected-source equations
and strict enclosure margins. Missing table entries are derived from neither
fallback signs nor an assumed accepted presentation. -/
theorem checkPresentation_complete (real : s.meetsRealAxis = true)
    {n : Nat} (sourcePolynomials : Fin n → DensePoly Rat)
    (sourceSquares : Fin n → DyadicSquare) (coordinates : Fin n → E)
    (keys : List E) (table : LiteralSign.Table E)
    (built : FieldBuild.buildTable p s hw hp keys = some table)
    (included : ∀ i, discSlack (sourceSquares i) (coordinates i) ∈ keys)
    (equations : ∀ i, (LiteralSign.realPoly (sourcePolynomials i)).IsRoot
      (Field.value (Field.literalRep p s hw hp) (coordinates i)))
    (margins : ∀ i, 0 < Field.value (Field.literalRep p s hw hp)
      (discSlack (sourceSquares i) (coordinates i))) :
    checkPresentation hw hp table sourcePolynomials sourceSquares coordinates = true := by
  have header := FieldBuild.buildTable_checked p s hw hp keys table built
  simp only [checkPresentation, Bool.and_eq_true, List.all_eq_true]
  refine ⟨header, ?_⟩
  intro i _
  refine ⟨checkEquation_complete real _ _ (equations i), ?_⟩
  have present := FieldBuild.buildTable_lookup p s hw hp keys table built
    (discSlack (sourceSquares i) (coordinates i)) (included i)
  obtain ⟨observed, found⟩ := Option.isSome_iff_exists.mp present
  have exactSign := Field.checkSignTable_lookup p s hw hp table header
    (discSlack (sourceSquares i) (coordinates i)) observed found
  have positive : SignType.sign (Field.value (Field.literalRep p s hw hp)
      (discSlack (sourceSquares i) (coordinates i))) = 1 :=
    sign_eq_one_iff.mpr (margins i)
  have one : observed = 1 := by simpa [positive] using exactSign
  simp only [found, one, beq_self_eq_true]

/-- Real source equations and strict selected-root margins suffice for actual
accepted presentation production, including an empty source list. All sign
evidence is constructed by the existing exact-field builder. -/
theorem build_complete (real : s.meetsRealAxis = true)
    {n : Nat} (sourcePolynomials : Fin n → DensePoly Rat)
    (sourceSquares : Fin n → DyadicSquare) (coordinates : Fin n → E)
    (equations : ∀ i, (LiteralSign.realPoly (sourcePolynomials i)).IsRoot
      (Field.value (Field.literalRep p s hw hp) (coordinates i)))
    (margins : ∀ i, 0 < Field.value (Field.literalRep p s hw hp)
      (discSlack (sourceSquares i) (coordinates i))) :
    ∃ table, FieldBuild.buildTable p s hw hp
        ((List.finRange n).map fun i => discSlack (sourceSquares i) (coordinates i)) = some table ∧
      checkPresentation hw hp table sourcePolynomials sourceSquares coordinates = true := by
  let keys := (List.finRange n).map fun i => discSlack (sourceSquares i) (coordinates i)
  obtain ⟨table, built⟩ := FieldBuild.buildTable_success p s hw hp real keys
  refine ⟨table, built, checkPresentation_complete real sourcePolynomials sourceSquares
    coordinates keys table built ?_ equations margins⟩
  intro i
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

end Hex.RCF.RealCoefficients.CommonPresentation
