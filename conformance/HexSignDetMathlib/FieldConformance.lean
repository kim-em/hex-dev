/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.SelectedProducer
public import HexSignDetMathlib.CompletionProducer
public import HexSignDetMathlib.QueryHandle
public import HexSignDetMathlib.RootList
public import HexSignDetMathlib.TableProducer
public import HexSignDetMathlib.ReencodingProducer
public import HexSignDetMathlib.ReencodingRefinement
public import HexSignDetMathlib.ThomReencoding
public import HexSignDetMathlib.ComparisonProducer
public import HexSignDetMathlib.Convert
public import HexSignDetMathlib.Embedding
public import HexRCF.RealCoefficients.CubeTwo
public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRealRootsMathlib.RealClosed
public import HexRealRootsMathlib.TarskiTests
public import HexRealAlgebraicMathlib.FieldSign
public import HexRealAlgebraicMathlib.Order
public import HexRealAlgebraicMathlib.RealClosed

public section

/-! Semantic sign-determination theorems instantiated over the actual cubic
number field ℚ(∛2) with its selected real embedding, and over a noninjective
coefficient carrier without a field instance. One instantiation per producer
correctness theorem checks that the Mathlib correctness API composes with real
number-field coefficients. The computations themselves are checked by the
compiled `hexsigndet_field_checks` executable. -/
namespace Hex.SignDetMathlib.FieldConformance

open Hex Hex.SignDet Hex.RCF.RealCoefficients HexPolyMathlib.Interpret HexRealRootsMathlib

abbrev generator := CubeTwo.realAlgebraic
abbrev CubicField := QAdjoin generator.toAlgebraic

/-- Interval evaluation computes the sign in the selected cubic embedding. -/
def fieldSign (a : CubicField) : Int := generator.signField a

abbrev rep := generator.toAlgebraic.rep
theorem real : rep.root.im = 0 :=
  (AlgebraicNumber.isReal_iff generator.toAlgebraic).mp generator.property
theorem binding : SimpleRoot.mk rep = generator.toAlgebraic.x :=
  generator.toAlgebraic.rep_mk

theorem sign_spec (a : CubicField) :
    fieldSign a = (SignType.sign (Field.value rep a) : Int) := by
  have same : fieldSign a = (Coefficients.ofField generator a).sign :=
    RealAlgebraicNumber.signField_eq generator a (Coefficients.ofField generator a).property
  rw [same, RealAlgebraicNumber.sign_eq, Field.ofField_value]
  by_cases hn : Field.value rep a < 0
  · simp only [hn, ↓reduceIte, sign_eq_neg_one_iff.mpr hn]
    rfl
  · by_cases hz : Field.value rep a = 0
    · simp [hz]
    · have hp : 0 < Field.value rep a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp only [hn, hz, ↓reduceIte, sign_eq_one_iff.mpr hp]
      rfl

/-- Negation respects the selected real embedding of the actual cubic field. -/
theorem value_neg (a : CubicField) : Field.value rep (-a) = -Field.value rep a := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_neg, Field.value_complex rep binding real,
    Field.value_complex rep binding real, PolyQuot.map_neg]

/-- The selected root of a cubic-field descriptor in the field's real embedding. -/
noncomputable abbrev root {context : Nat} (d : Descriptor CubicField Nat fieldSign context) : ℝ :=
  d.root (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec

/-- Selected signs: every query list succeeds with the real evaluation signs. -/
theorem cubic_success (d : Descriptor CubicField Nat fieldSign 7)
    (qs : List (DensePoly CubicField)) :
    ∃ s : SelectedSigns d qs, d.buildSigns qs = .ok s ∧
      s.values.toList = signsAt (Field.value rep)
        (Field.value_eq_zero rep binding real) qs (root d) :=
  d.buildSigns_roots (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) qs

/-- Completion preserves the root and records its full derivative word. -/
theorem cubic_complete (d : Descriptor CubicField Nat fieldSign 7) :
    root d.complete = root d ∧
      d.raw.completes d.complete.raw = true ∧
      d.complete.raw.indices = (List.range d.raw.head.natDegree).map (· + 1) ∧
      d.complete.raw.signs = (List.range d.raw.head.natDegree).map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j + 1]
          (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)).eval
          (root d)) : Int)) :=
  d.complete_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real)

/-- Prepared query handles preserve the original selected root. -/
theorem cubic_queries (d : Descriptor CubicField Nat fieldSign 7) (h : QueryHandle d)
    (qs : List (DensePoly CubicField)) :
    ∃ s : SelectedSigns d qs, h.buildSigns qs = .ok s ∧
      s.values.toList = signsAt (Field.value rep)
        (Field.value_eq_zero rep binding real) qs (root d) :=
  h.buildSigns_roots (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) qs

/-- Root lists cover precisely the mathematical roots, without repetitions. -/
theorem cubic_coverage (p : DensePoly CubicField) (a b : Endpoint CubicField)
    (out : List (Descriptor CubicField Nat fieldSign 7))
    (h : Descriptor.buildRoots fieldSign 7 p a b = .ok (some out)) :
    (∀ x, x ∈ Tarski.rootsIn
      (interpret (Field.value rep) (Field.value_eq_zero rep binding real) p)
      (a.map (Field.value rep)) (b.map (Field.value rep)) ↔ x ∈ out.map root) ∧
    (out.map root).Nodup :=
  Descriptor.buildRoots_coverage (Field.value rep)
    (Field.value_eq_zero rep binding real) (Field.value_one rep binding real)
    (Field.value_add rep binding real) (Field.value_sub rep binding real)
    (Field.value_mul rep binding real) (Field.value_natCast rep binding real) sign_spec h

/-- Successful tables have the exact real root counts for every sign word. -/
theorem cubic_table (p : DensePoly CubicField) (a b : Endpoint CubicField)
    (qs : List (DensePoly CubicField)) (reduced : Bool) (table : SignTable qs.length)
    (h : determine fieldSign 7 p a b qs reduced = some table) :
    HexSturmMathlib.Domain (Field.value rep) (Field.value_eq_zero rep binding real) p a b ∧
      ∀ word, table.count word =
        ((Tarski.rootsIn
          (interpret (Field.value rep) (Field.value_eq_zero rep binding real) p)
          (a.map (Field.value rep)) (b.map (Field.value rep))).filter
          (fun x => signsAt (Field.value rep) (Field.value_eq_zero rep binding real)
            qs x = word)).card :=
  determine_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) value_neg (Field.value_inv rep binding real)
    fieldSign sign_spec 7 p a b qs reduced table h

/-- Total comparison is the real order of the selected roots. -/
theorem cubic_compare (left right : Descriptor CubicField Nat fieldSign 7) :
    left.compare right =
      (if root left < root right then .lt else if root right < root left then .gt else .eq) :=
  left.compare_correct (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) (Field.value_div rep binding real) right

/-- Re-encoding reports absence whenever the selected root is not a target root. -/
theorem cubic_absent (d : Descriptor CubicField Nat fieldSign 7)
    (target : DensePoly CubicField) (a b : Endpoint CubicField)
    (habsent : root d ∉
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) target)
        (a.map (Field.value rep)) (b.map (Field.value rep))) :
    d.buildReencoding target a b = .ok none :=
  d.buildReencoding_absent (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) target a b habsent

/-- Refinement to any contained valid interval succeeds with the same root. -/
theorem cubic_refinement (d : Descriptor CubicField Nat fieldSign 7)
    (a b : Endpoint CubicField)
    (hdom : HexSturmMathlib.Domain (Field.value rep) (Field.value_eq_zero rep binding real)
      d.raw.head a b)
    (hmem : root d ∈
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (a.map (Field.value rep)) (b.map (Field.value rep)))
    (hsubset : Tarski.rootsIn
      (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (a.map (Field.value rep)) (b.map (Field.value rep)) ⊆
      Tarski.rootsIn (interpret (Field.value rep) (Field.value_eq_zero rep binding real) d.raw.head)
        (d.raw.lower.map (Field.value rep)) (d.raw.upper.map (Field.value rep))) :
    ∃ r : Reencoding d d.raw.head a b,
      d.buildReencoding d.raw.head a b = .ok (some r) ∧ root r.target = root d :=
  d.buildReencoding_refinement (Field.value rep) (Field.value_eq_zero rep binding real)
    (Field.value_one rep binding real) (Field.value_add rep binding real)
    (Field.value_sub rep binding real) (Field.value_mul rep binding real)
    (Field.value_natCast rep binding real) sign_spec value_neg
    (Field.value_inv rep binding real) a b hdom hmem hsubset

/-- Rational signs are the signs of their real casts. -/
theorem rational_sign (q : Rat) : Sturm.orderSign q = (SignType.sign (q : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono q).symm

/-- Zero reflection for the rational embedding into the cubic field. -/
theorem cubic_zero (q : Rat) : (PolyQuot.ofRat q : CubicField) = 0 ↔ q = 0 := by
  rw [← Field.value_eq_zero rep binding real,
    FieldSpecialize.value_ofRat rep binding real, Rat.cast_eq_zero]

/-- Conversion of a rational descriptor into the cubic field selects the same root. -/
theorem cubic_convert (source : Descriptor Rat Nat Sturm.orderSign 7)
    (target : Descriptor CubicField Nat fieldSign 8)
    (h : source.convert PolyQuot.ofRat cubic_zero fieldSign 8 = .ok (.ok target)) :
    root target =
      source.root (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
        Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
        (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _) rational_sign :=
  source.convert_root (f := fun q : Rat => (q : ℝ))
    (hfz := fun _ => Rat.cast_eq_zero)
    (g := Field.value rep) (hgz := Field.value_eq_zero rep binding real)
    (convert := PolyQuot.ofRat) (hcz := cubic_zero) (newSign := fieldSign)
    (hvalue := FieldSpecialize.value_ofRat rep binding real)
    (hfnat := fun _ => Rat.cast_natCast _) (hfm := fun _ _ => Rat.cast_mul _ _)
    (hgnat := Field.value_natCast rep binding real) (hgm := Field.value_mul rep binding real)
    (hf1 := Rat.cast_one) (hfa := fun _ _ => Rat.cast_add _ _)
    (hfs := fun _ _ => Rat.cast_sub _ _) (hfsign := rational_sign)
    (hg1 := Field.value_one rep binding real) (hga := Field.value_add rep binding real)
    (hgs := Field.value_sub rep binding real) (hgsign := sign_spec) 8 target h

/-- Rational signs agree in Hex's concrete real closed algebraic field. -/
theorem algebraic_sign (q : Rat) : Sturm.orderSign q =
    (SignType.sign (q : RealAlgebraicNumber) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom RealAlgebraicNumber)
    Rat.cast_strictMono q).symm

/-- A rational descriptor selects the same root in the concrete real algebraic
field and in ℝ through the proved order embedding. -/
theorem algebraic_root (d : Descriptor Rat Nat Sturm.orderSign 7) :
    RealAlgebraicNumber.toRealHom
        (d.root (fun q : Rat => (q : RealAlgebraicNumber)) (fun _ => Rat.cast_eq_zero)
          Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
          (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _) algebraic_sign) =
      d.root (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
        Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
        (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _) rational_sign := by
  symm
  exact d.root_map (fun q : Rat => (q : RealAlgebraicNumber)) (fun _ => Rat.cast_eq_zero)
    (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero) RealAlgebraicNumber.toRealHom
    RealAlgebraicNumber.toRealOrderEmbedding.strictMono
    (fun q => (map_ratCast RealAlgebraicNumber.toRealHom q).symm)
    Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _)
    Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _)
    algebraic_sign rational_sign

namespace Noncanonical

open HexPoly.InterpretTests

/-- Real interpretation of a carrier with canonical zero and several stored
representations of each nonzero value. It has no field instance. -/
@[expose] def realValue (a : Rep) : ℝ := (value a : ℝ)
theorem zero (a : Rep) : realValue a = 0 ↔ a = 0 := by
  simp only [realValue, Rat.cast_eq_zero, value_eq_zero]
theorem one : realValue 1 = 1 := by simp [realValue, value_one]
theorem add (a b : Rep) : realValue (a + b) = realValue a + realValue b := by
  simp [realValue, value_add, Rat.cast_add]
theorem sub (a b : Rep) : realValue (a - b) = realValue a - realValue b := by
  simp [realValue, value_sub, Rat.cast_sub]
theorem mul (a b : Rep) : realValue (a * b) = realValue a * realValue b := by
  simp [realValue, value_mul, Rat.cast_mul]
theorem natCast (n : Nat) : realValue (n : Rep) = (n : ℝ) := by
  simp [realValue, value_natCast]
theorem neg (a : Rep) : realValue (-a) = -realValue a := by
  have h : value (-a) = -value a := by
    change value (pack (-(HexPoly.InterpretTests.raw a).1)
      (-(HexPoly.InterpretTests.raw a).2)) = -value a
    rw [value_pack]
    exact (neg_add _ _).symm
  simp [realValue, h]
theorem inv (a : Rep) : realValue a⁻¹ = (realValue a)⁻¹ := by
  simp [realValue, value_inv, Rat.cast_inv]
theorem sign (a : Rep) : Hex.TarskiTests.Noncanonical.sign a =
    (SignType.sign (realValue a) : Int) := by
  have hr : Hex.TarskiTests.Noncanonical.sign a = (SignType.sign (value a) : Int) := by
    by_cases hn : value a < 0
    · simp only [Hex.TarskiTests.Noncanonical.sign,
        Int.sign_eq_neg_one_of_neg (Rat.num_neg.mpr hn), sign_eq_neg_one_iff.mpr hn]
      rfl
    · by_cases hz : value a = 0
      · simp [Hex.TarskiTests.Noncanonical.sign, hz]
      · have hp : 0 < value a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
        simp only [Hex.TarskiTests.Noncanonical.sign,
          Int.sign_eq_one_of_pos (Rat.num_pos.mpr hp), sign_eq_one_iff.mpr hp]
        rfl
  rw [hr]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono (value a)).symm

/-- Re-encoding to any valid target containing the root succeeds over the
noninjective carrier; no head equality or old-domain containment is assumed. -/
theorem reencoding (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7)
    (head : DensePoly Rep) (a b : Endpoint Rep)
    (hdom : HexSturmMathlib.Domain realValue zero head a b)
    (hmem : d.root realValue zero one add sub mul natCast sign ∈
      Tarski.rootsIn (interpret realValue zero head) (a.map realValue) (b.map realValue)) :
    ∃ r : Reencoding d head a b,
      d.buildReencoding head a b = .ok (some r) ∧
      r.target.root realValue zero one add sub mul natCast sign =
        d.root realValue zero one add sub mul natCast sign :=
  d.buildReencoding_success realValue zero one add sub mul natCast sign neg inv
    head a b hdom hmem

/-- The embedding interface applies to the noninjective carrier, deriving all
laws in an arbitrary ordered real closed extension of ℝ. -/
theorem extension_root {L : Type*} [_root_.Field L] [DecidableEq L] [LinearOrder L]
    [IsStrictOrderedRing L] [IsRealClosed L] (ι : ℝ →+* L) (hι : StrictMono ι)
    (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7) :
    ∃ x : L,
      x ∈ Tarski.rootsIn
        (interpret (fun a => ι (realValue a)) (fun a => (map_eq_zero ι).trans (zero a))
          d.raw.head)
        (d.raw.lower.map fun a => ι (realValue a))
        (d.raw.upper.map fun a => ι (realValue a)) ∧
      signsAt (fun a => ι (realValue a)) (fun a => (map_eq_zero ι).trans (zero a))
        d.raw.queries x = d.raw.signs ∧
      x = ι (d.root realValue zero one add sub mul natCast sign) := by
  let g := fun a => ι (realValue a)
  have hz : ∀ a, g a = 0 ↔ a = 0 := fun a => (map_eq_zero ι).trans (zero a)
  have h1 : g 1 = 1 := by simp [g, one]
  have ha : ∀ a b, g (a + b) = g a + g b := by simp [g, add]
  have hs : ∀ a b, g (a - b) = g a - g b := by simp [g, sub]
  have hm : ∀ a b, g (a * b) = g a * g b := by simp [g, mul]
  have hn : ∀ n : Nat, g (n : Rep) = (n : L) := by simp [g, natCast]
  have hsign : ∀ a, Hex.TarskiTests.Noncanonical.sign a = (SignType.sign (g a) : Int) := by
    intro a
    dsimp only [g]
    rw [hι.sign_comp]
    exact sign a
  obtain ⟨hx, hword⟩ := d.root_spec g hz h1 ha hs hm hn hsign
  refine ⟨d.root g hz h1 ha hs hm hn hsign, hx, hword, ?_⟩
  exact d.root_comp realValue zero ι hι one add sub mul natCast sign

end Noncanonical

/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_success
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_complete
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_queries
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_coverage
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_table
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_compare
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_absent
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_refinement
/-- info: 'Hex.SignDetMathlib.FieldConformance.cubic_convert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_convert
/-- info: 'Hex.SignDetMathlib.FieldConformance.algebraic_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraic_root
/-- info: 'Hex.SignDetMathlib.FieldConformance.Noncanonical.reencoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.reencoding
/-- info: 'Hex.SignDetMathlib.FieldConformance.Noncanonical.extension_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.extension_root

end Hex.SignDetMathlib.FieldConformance
