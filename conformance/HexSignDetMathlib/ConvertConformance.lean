/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Convert
public import HexSignDetMathlib.Embedding
public import HexSignDetMathlib.ReencodingConformance
public import HexSignDet.Infinitesimal
public import HexRCF.RealCoefficients.FieldSpecialize
public meta import HexSignDet.Infinitesimal
public meta import HexSignDet
public meta import HexPoly.InterpretTests
public meta import HexRealRootsMathlib.TarskiTests
public meta import HexSignDetMathlib.SelectedProducerConformance
public meta import HexNumberField
public meta import HexRCF.RealCoefficients.Coefficients

public section

/-! Checked representation and context changes through the actual descriptor
builder. Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.ConvertConformance

open Hex Hex.SignDet HexPoly.InterpretTests HexPolyMathlib.Interpret
open Hex.RCF.RealCoefficients Hex.SignDetMathlib.SelectedProducerConformance

/-- Rationalization merges different nonzero coefficient representations while
retaining the partial word and constructing new evidence in context 8. -/
def rationalizes (source : RawDescriptor Rep Nat) (expected : Int) : Bool :=
  match Descriptor.validate Hex.TarskiTests.Noncanonical.sign 7 source with
  | none => false
  | some d =>
    match d.convert value value_eq_zero Sturm.orderSign 8 with
    | .ok (.ok target) =>
      target.raw.context == 8 &&
      target.raw.head == DensePoly.Interpret.map value value_eq_zero source.head &&
      target.raw.lower == source.lower.map value &&
      target.raw.upper == source.upper.map value &&
      target.raw.indices == source.indices && target.raw.signs == source.signs &&
      target.raw.check Sturm.orderSign 8 target.evidence &&
      !({target.raw with context := 7}).check Sturm.orderSign 7 target.evidence &&
      !({target.raw with indices := [0]}).check Sturm.orderSign 8 target.evidence &&
      target.signAt (DensePoly.ofList [-1, 1]) == expected &&
      target.signAt (DensePoly.ofList [-1, 0, 1]) == 0
    | _ => false

/-- Distinct representations of one are present in the source itself. -/
def noncanonicalRaw : RawDescriptor Rep Nat :=
  ⟨7, x*x - DensePoly.C root, .negInf, .posInf, [1], [1]⟩

#guard root != (1 : Rep)
#guard value root == value (1 : Rep)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rationalizes noncanonicalRaw 0
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rationalizes {noncanonicalRaw with signs := [-1]} (-1)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard rationalizes {noncanonicalRaw with lower := .finite 0, upper := .finite (pack 0 2), indices := [], signs := []} 0

/-- A context-only conversion over the actual nonquadratic QAdjoin field
rebuilds child queries even when head, bounds and derivative signs are identical. -/
def cubicContextPasses : Bool :=
  let raw := {Hex.SignDetMathlib.SelectedProducerConformance.raw with
    indices := [1, 2], signs := [1, 1]}
  match Descriptor.validate fieldSign 7 raw with
  | none => false
  | some source =>
    match source.convert id (fun _ => Iff.rfl) fieldSign 8 with
    | .ok (.ok target) =>
      let staleChildRejected := match source.evidence, target.evidence with
        | .split _ oldLeft _, .split node _ freshRight =>
          !target.raw.check fieldSign 8 (.split node oldLeft freshRight)
        | _, _ => false
      staleChildRejected &&
      target.raw.context == 8 && target.raw.head == source.raw.head &&
      target.raw.lower == source.raw.lower && target.raw.upper == source.raw.upper &&
      target.raw.indices == source.raw.indices && target.raw.signs == source.raw.signs &&
      target.raw.check fieldSign 8 target.evidence &&
      !target.raw.check fieldSign 8 source.evidence &&
      !({source.raw with context := 8}).check fieldSign 8 source.evidence &&
      !({target.raw with context := 7}).check fieldSign 7 target.evidence &&
      target.signAt (xPoly.natPow 3 - DensePoly.C 2) == 0 &&
      target.signAt (xPoly - 1) == 1
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard cubicContextPasses

/-- Zero reflection for the existing rational embedding into the cubic field. -/
theorem cubic_zero (q : Rat) : (PolyQuot.ofRat q : CubicField) = 0 ↔ q = 0 := by
  rw [← Field.value_eq_zero rep binding real,
    FieldSpecialize.value_ofRat rep binding real, Rat.cast_eq_zero]

/-- A converter need not preserve values; the existing builder reports its
ordinary domain error when the converted finite bounds are reversed. -/
def badConversionPasses : Bool :=
  let raw : RawDescriptor Rat Nat :=
    ⟨7, DensePoly.ofList [-2, 0, 1], .finite 1, .finite 2, [], []⟩
  match Descriptor.validate Sturm.orderSign 7 raw with
  | none => false
  | some source =>
    match source.convert (fun q => -q) (fun _ => neg_eq_zero) Sturm.orderSign 8 with
    | .ok (.error .domain) => true
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard badConversionPasses

/-- Move a rational root descriptor into the actual cubic coefficient field.
The selected root is √2; comparison with ∛2 is then an ordinary selected sign. -/
def intoCubicPasses : Bool :=
  let raw : RawDescriptor Rat Nat :=
    ⟨7, DensePoly.ofList [-2, 0, 1], .finite 0, .posInf, [], []⟩
  match Descriptor.validate Sturm.orderSign 7 raw with
  | none => false
  | some source =>
    match source.convert PolyQuot.ofRat cubic_zero fieldSign 8 with
    | .ok (.ok target) =>
      target.raw.context == 8 && target.raw.indices.isEmpty && target.raw.signs.isEmpty &&
      target.raw.lower == .finite 0 && target.raw.upper == .posInf &&
      target.signAt (xPoly - DensePoly.C alpha) == 1 &&
      target.signAt (xPoly.natPow 2 - DensePoly.C 2) == 0
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard intoCubicPasses

/-- Executable context-only conversion for a root trapped between nested
infinitesimal bounds. This fixture supplies no real-closed interpretation. -/
def nestedContextPasses : Bool :=
  let sourceRaw : RawDescriptor Infinitesimal.Second Nat :=
    ⟨7, Infinitesimal.nested, .finite 0, .finite (2 * Infinitesimal.delta), [], []⟩
  match Descriptor.validate Infinitesimal.secondSign 7 sourceRaw with
  | none => false
  | some source =>
    match source.convert id (fun _ => Iff.rfl) Infinitesimal.secondSign 8 with
    | .ok (.ok target) =>
      target.raw.context == 8 && target.raw.head == sourceRaw.head &&
      target.raw.lower == sourceRaw.lower && target.raw.upper == sourceRaw.upper &&
      !target.raw.check Infinitesimal.secondSign 8 source.evidence &&
      !({sourceRaw with context := 8}).check Infinitesimal.secondSign 8 source.evidence &&
      target.signAt (Infinitesimal.x - DensePoly.C Infinitesimal.delta) == 0
    | _ => false

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
#guard nestedContextPasses

namespace Noncanonical

open Hex.SignDetMathlib.ReencodingConformance.Noncanonical

theorem rational_sign (q : Rat) : Sturm.orderSign q = (SignType.sign (q : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono q).symm

/-- The semantic theorem applies to every validated noncanonical descriptor,
not only to the finite fixtures above. -/
theorem success (source : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7) :
    ∃ target, source.convert value value_eq_zero Sturm.orderSign 8 = .ok (.ok target) := by
  exact source.convert_success (f := realValue) (hfz := zero)
    (g := fun q : Rat => (q : ℝ)) (hgz := fun _ => Rat.cast_eq_zero)
    (convert := value) (hcz := value_eq_zero) (newSign := Sturm.orderSign)
    (hvalue := by intro a; unfold realValue; rfl) (hfnat := natCast) (hfm := mul)
    (hgnat := fun _ => Rat.cast_natCast _) (hgm := fun _ _ => Rat.cast_mul _ _)
    (hf1 := one) (hfa := add) (hfs := sub) (hfsign := sign)
    (hg1 := Rat.cast_one) (hga := fun _ _ => Rat.cast_add _ _)
    (hgs := fun _ _ => Rat.cast_sub _ _) (hgn := fun _ => Rat.cast_neg _)
    (hgi := fun _ => Rat.cast_inv _) (hgsign := rational_sign) 8

theorem root (source : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7)
    (target : Descriptor Rat Nat Sturm.orderSign 8)
    (h : source.convert value value_eq_zero Sturm.orderSign 8 = .ok (.ok target)) :
    target.root (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
        Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
        (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _) rational_sign =
      source.root realValue zero one add sub mul natCast sign := by
  exact source.convert_root (f := realValue) (hfz := zero)
    (g := fun q : Rat => (q : ℝ)) (hgz := fun _ => Rat.cast_eq_zero)
    (convert := value) (hcz := value_eq_zero) (newSign := Sturm.orderSign)
    (hvalue := by intro a; unfold realValue; rfl) (hfnat := natCast) (hfm := mul)
    (hgnat := fun _ => Rat.cast_natCast _) (hgm := fun _ _ => Rat.cast_mul _ _)
    (hf1 := one) (hfa := add) (hfs := sub) (hfsign := sign)
    (hg1 := Rat.cast_one) (hga := fun _ _ => Rat.cast_add _ _)
    (hgs := fun _ _ => Rat.cast_sub _ _) (hgsign := rational_sign) 8 target h

end Noncanonical

/-- The embedding interface applies to the actual noninjective coefficient
carrier, deriving all laws in an arbitrary ordered real closed extension. -/
theorem extension_root {L : Type*} [Field L] [DecidableEq L] [LinearOrder L]
    [IsStrictOrderedRing L] [IsRealClosed L] (ι : ℝ →+* L) (hι : StrictMono ι)
    (d : Descriptor Rep Nat Hex.TarskiTests.Noncanonical.sign 7) :
    ∃ x : L,
      x ∈ HexRealRootsMathlib.Tarski.rootsIn
        (interpret (fun a => ι (ReencodingConformance.Noncanonical.realValue a))
          (fun a => (map_eq_zero ι).trans (ReencodingConformance.Noncanonical.zero a))
          d.raw.head)
        (d.raw.lower.map fun a => ι (ReencodingConformance.Noncanonical.realValue a))
        (d.raw.upper.map fun a => ι (ReencodingConformance.Noncanonical.realValue a)) ∧
      signsAt (fun a => ι (ReencodingConformance.Noncanonical.realValue a))
        (fun a => (map_eq_zero ι).trans (ReencodingConformance.Noncanonical.zero a))
        d.raw.queries x = d.raw.signs ∧
      x = ι (d.root ReencodingConformance.Noncanonical.realValue
        ReencodingConformance.Noncanonical.zero ReencodingConformance.Noncanonical.one
        ReencodingConformance.Noncanonical.add ReencodingConformance.Noncanonical.sub
        ReencodingConformance.Noncanonical.mul ReencodingConformance.Noncanonical.natCast
        ReencodingConformance.Noncanonical.sign) := by
  let g := fun a => ι (ReencodingConformance.Noncanonical.realValue a)
  have hz : ∀ a, g a = 0 ↔ a = 0 := fun a =>
    (map_eq_zero ι).trans (ReencodingConformance.Noncanonical.zero a)
  have h1 : g 1 = 1 := by simp [g, ReencodingConformance.Noncanonical.one]
  have ha : ∀ a b, g (a + b) = g a + g b := by
    simp [g, ReencodingConformance.Noncanonical.add]
  have hs : ∀ a b, g (a - b) = g a - g b := by
    simp [g, ReencodingConformance.Noncanonical.sub]
  have hm : ∀ a b, g (a * b) = g a * g b := by
    simp [g, ReencodingConformance.Noncanonical.mul]
  have hn : ∀ n : Nat, g (n : Rep) = (n : L) := by
    simp [g, ReencodingConformance.Noncanonical.natCast]
  have hsign : ∀ a, Hex.TarskiTests.Noncanonical.sign a = (SignType.sign (g a) : Int) := by
    intro a
    dsimp only [g]
    rw [hι.sign_comp]
    exact ReencodingConformance.Noncanonical.sign a
  obtain ⟨hx, hword⟩ := d.root_spec g hz h1 ha hs hm hn hsign
  refine ⟨d.root g hz h1 ha hs hm hn hsign, hx, hword, ?_⟩
  exact d.root_comp ReencodingConformance.Noncanonical.realValue
    ReencodingConformance.Noncanonical.zero ι hι ReencodingConformance.Noncanonical.one
    ReencodingConformance.Noncanonical.add ReencodingConformance.Noncanonical.sub
    ReencodingConformance.Noncanonical.mul ReencodingConformance.Noncanonical.natCast
    ReencodingConformance.Noncanonical.sign

/-- The rational-to-cubic embedding satisfies the production success theorem
for every validated source, independently of the particular test inputs. -/
theorem cubic_success (source : Descriptor Rat Nat Sturm.orderSign 7) :
    ∃ target, source.convert PolyQuot.ofRat cubic_zero fieldSign 8 = .ok (.ok target) := by
  exact source.convert_success (f := fun q : Rat => (q : ℝ))
    (hfz := fun _ => Rat.cast_eq_zero)
    (g := Field.value rep) (hgz := Field.value_eq_zero rep binding real)
    (convert := PolyQuot.ofRat) (hcz := cubic_zero) (newSign := fieldSign)
    (hvalue := FieldSpecialize.value_ofRat rep binding real) (hfnat := fun _ => Rat.cast_natCast _)
    (hfm := fun _ _ => Rat.cast_mul _ _) (hgnat := Field.value_natCast rep binding real)
    (hgm := Field.value_mul rep binding real)
    (hf1 := Rat.cast_one) (hfa := fun _ _ => Rat.cast_add _ _)
    (hfs := fun _ _ => Rat.cast_sub _ _) (hfsign := Noncanonical.rational_sign)
    (hg1 := Field.value_one rep binding real) (hga := Field.value_add rep binding real)
    (hgs := Field.value_sub rep binding real) (hgn := value_neg)
    (hgi := Field.value_inv rep binding real) (hgsign := sign_spec) 8

/-- The converted descriptor selects the same mathematical root in the actual
cubic coefficient field, for every successful checked conversion. -/
theorem cubic_root (source : Descriptor Rat Nat Sturm.orderSign 7)
    (target : Descriptor CubicField Nat fieldSign 8)
    (h : source.convert PolyQuot.ofRat cubic_zero fieldSign 8 = .ok (.ok target)) :
    target.root (Field.value rep) (Field.value_eq_zero rep binding real)
        (Field.value_one rep binding real) (Field.value_add rep binding real)
        (Field.value_sub rep binding real) (Field.value_mul rep binding real)
        (Field.value_natCast rep binding real) sign_spec =
      source.root (fun q : Rat => (q : ℝ)) (fun _ => Rat.cast_eq_zero)
        Rat.cast_one (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
        (fun _ _ => Rat.cast_mul _ _) (fun _ => Rat.cast_natCast _)
        Noncanonical.rational_sign := by
  exact source.convert_root (f := fun q : Rat => (q : ℝ))
    (hfz := fun _ => Rat.cast_eq_zero)
    (g := Field.value rep) (hgz := Field.value_eq_zero rep binding real)
    (convert := PolyQuot.ofRat) (hcz := cubic_zero) (newSign := fieldSign)
    (hvalue := FieldSpecialize.value_ofRat rep binding real)
    (hfnat := fun _ => Rat.cast_natCast _) (hfm := fun _ _ => Rat.cast_mul _ _)
    (hgnat := Field.value_natCast rep binding real) (hgm := Field.value_mul rep binding real)
    (hf1 := Rat.cast_one) (hfa := fun _ _ => Rat.cast_add _ _)
    (hfs := fun _ _ => Rat.cast_sub _ _) (hfsign := Noncanonical.rational_sign)
    (hg1 := Field.value_one rep binding real) (hga := Field.value_add rep binding real)
    (hgs := Field.value_sub rep binding real) (hgsign := sign_spec) 8 target h

/-- info: 'Hex.SignDet.RawDescriptor.map_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.map_wellFormed
/-- info: 'Hex.SignDet.Descriptor.convert_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.convert_success
/-- info: 'Hex.SignDet.Descriptor.convert_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.convert_root
/-- info: 'Hex.SignDetMathlib.ConvertConformance.Noncanonical.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.success
/-- info: 'Hex.SignDetMathlib.ConvertConformance.Noncanonical.root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Noncanonical.root

/-- info: 'Hex.SignDetMathlib.ConvertConformance.cubic_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_success
/-- info: 'Hex.SignDetMathlib.ConvertConformance.cubic_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_root
/-- info: 'Hex.SignDetMathlib.ConvertConformance.cubic_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_zero

/-- info: 'Hex.SignDet.Descriptor.root_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.root_map
/-- info: 'Hex.SignDet.Descriptor.root_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.root_comp
/-- info: 'Hex.SignDetMathlib.ConvertConformance.extension_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extension_root

end Hex.SignDetMathlib.ConvertConformance
