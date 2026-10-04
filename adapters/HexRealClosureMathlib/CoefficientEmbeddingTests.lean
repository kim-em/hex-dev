/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CoefficientEmbedding
import all Init.Data.Array.Basic
import all HexRationalFn.Field
import all HexSignDet.Descriptor
import all HexSignDet.SelectedSigns
import all HexSignDet.Table

public section

namespace Hex.RealClosure.Specialize.EmbeddingTests
open Hex Hex.SignDet
section NativeData
local instance (priority := 4000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance (priority := 4000) : Lean.Grind.Field (RationalFn Rat) := RationalFn.instField
local instance (priority := 4000) : Lean.Grind.Field (RationalFn (RationalFn Rat)) := RationalFn.instField

abbrev First := RationalFn Rat
abbrev Second := RationalFn First
@[expose] def sign : Second → Int :=
  OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign)
def x : DensePoly Second := DensePoly.ofCoeffs #[0, 1]
def epsilon : Second := RationalFn.C RationalFn.X
def a : Second := 2 + epsilon + RationalFn.X
def head : DensePoly Second := x * x - DensePoly.C a
def raw : RawDescriptor Second Unit :=
  { context := (), head,
    lower := .finite 1, upper := .finite 2, indices := [], signs := [] }

/-- Literal fraction-free identities for `X²-(2+ε+δ)`, independently checked
against the native coefficient operations. -/
def chain : SignedRemainderChain Second where
  chain := #[head, x, 1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 0, 2⟩
  steps := #[⟨1, x, a⟩]
  terminal := some (1, x)

def countQuery : TarskiCertificate Second Second Unit where
  context := ()
  head
  queryPoly := 1
  lower := .finite 1
  upper := .finite 2
  squarefree := chain
  remainders := chain
  lowerSigns := #[-1, 1, 1]
  upperSigns := #[1, 1, 1]
  lowerVariations := 1
  upperVariations := 0
  value := 1

def countNode : Node Second Unit where
  context := ()
  head
  lower := .finite 1
  upper := .finite 2
  queries := []
  size := 1
  system := {
    rows := #v[[]]
    columns := #v[[]]
    counts := #v[1]
    values := #v[1]
    inverse := Matrix.identity 1
    denominator := 1 }
  moments := #v[countQuery]
  reductions := #v[none]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide⟩]
    denom := 1
    adj := Matrix.identity 1 }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem countAccepted :
    (Replay.leaf countNode).check sign () raw.head raw.lower raw.upper raw.queries = true := by
  simp only [raw, RawDescriptor.queries, List.map_nil, Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

def descriptor : Descriptor Second Unit sign () :=
  Descriptor.ofTable raw (.leaf countNode) (by decide +kernel) rfl countAccepted (by
    rw [Replay.table_lookup]
    decide +kernel)

theorem descriptor_raw : descriptor.raw = raw := Descriptor.ofTable_raw _ _ _ _ _ _

def query : DensePoly Second := x - 1

def queryChain : SignedRemainderChain Second where
  chain := #[head, DensePoly.C a - x, -1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 2, 2⟩
  steps := #[⟨1, -x - DensePoly.C a, a * a - a⟩]
  terminal := some (1, x - DensePoly.C a)

def squareChain : SignedRemainderChain Second where
  chain := #[head, DensePoly.C (a + 1) * x - DensePoly.C (2 * a), 1]
  degrees := #[2, 1, 0]
  initial := ⟨1, 2 * x - DensePoly.C 4, 2⟩
  steps := #[⟨(a + 1) * (a + 1), DensePoly.C (a + 1) * x + DensePoly.C (2 * a),
    a * (a - 1) * (a - 1)⟩]
  terminal := some (1, DensePoly.C (a + 1) * x - DensePoly.C (2 * a))

def queryCertificate : TarskiCertificate Second Second Unit :=
  {countQuery with
    queryPoly := query
    remainders := queryChain
    lowerSigns := #[-1, 1, -1]
    upperSigns := #[1, 1, -1]
    lowerVariations := 2
    upperVariations := 1}

def squareCertificate : TarskiCertificate Second Second Unit :=
  {countQuery with
    queryPoly := query * query
    remainders := squareChain
    lowerSigns := #[-1, -1, 1]}

def selectedNode : Node Second Unit where
  context := ()
  head
  lower := .finite 1
  upper := .finite 2
  queries := [query]
  size := 3
  system := {
    rows := #v[[0], [1], [2]]
    columns := #v[[-1], [0], [1]]
    counts := #v[0, 0, 1]
    values := #v[1, 1, 1]
    denominator := 2
    inverse := Matrix.ofRows #v[#v[0, -1, 1], #v[2, 0, -2], #v[0, 1, 1]] }
  moments := #v[countQuery, queryCertificate, squareCertificate]
  basis := {
    rank := 1
    rows := #v[0]
    cols := #v[⟨0, by decide⟩]
    denom := 1
    adj := Matrix.identity 1 }

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem signsAccepted :
    raw.checkSigns sign () [query] #v[1] (.leaf selectedNode) = true := by
  simp only [RawDescriptor.checkSigns, Replay.check, Node.check_eq, checkMoment_eq,
    queryPoly, Sturm.check, TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

@[expose] def selected : SelectedSigns descriptor [query] where
  values := #v[1]
  evidence := .leaf selectedNode
  accepted := by
    unfold Descriptor.checkSigns
    rw [descriptor_raw]
    exact signsAccepted

end NativeData

theorem recorded_values : selected.values.toList = [1] := rfl

/-- Native nested checked evidence reaches one ordinary real parameter pair
and selected root, retaining the nonconstant query's recorded positive sign. -/
theorem ordinary_selected :
    let values := selected.values.toList
    letI : Lean.Grind.Field Rat := Field.toGrindField
    let data := Native.nestedEvidence (F := Rat) (context := ()) Lean.Grind.instFieldRat
      HexRationalFnMathlib.ratField_eq descriptor [query] selected
    let interpretation := CoefficientMap.ofHom
      (HexRationalFnMathlib.mapHom (HexRationalFnMathlib.mapHom (Rat.castHom ℝ)))
    HEq data.1 descriptor ∧ HEq data.2.1 [query] ∧ HEq data.2.2 selected ∧
    ∃ first second : ℝ, 0 < first ∧ first < 1 ∧ 0 < second ∧ second < first ∧
      ∃ target : Descriptor ℝ Unit (fun r : ℝ => (SignType.sign r : Int)) (),
        target.raw = ((data.1.raw.substitute interpretation).substitute (firstMap first)).specialize
          (RingHom.id ℝ) second ∧
        target.evidence = ((data.1.evidence.substitute interpretation).substitute (firstMap first)).specialize
          (RingHom.id ℝ) second ∧
        (∀ i, target.raw.head.coeff i =
          evalNestedFraction ((data.1.raw.substitute interpretation).head.coeff i) first second) ∧
        (∀ q ∈ data.2.1.map interpretation.polynomial, ∀ i,
          (polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second).coeff i =
            evalNestedFraction (q.coeff i) first second) ∧
        signsAt (fun r : ℝ => r) (fun _ => Iff.rfl)
          ((data.2.1.map interpretation.polynomial).map
            (fun q => polynomial (RingHom.id ℝ) ((firstMap first).polynomial q) second))
          (target.root (fun r : ℝ => r) (fun _ => Iff.rfl) rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ => rfl) (fun _ => rfl)) = values ∧
        let constant := (data.1.raw.substitute interpretation).head.coeff 0
        (firstMap first).map constant = mapFraction constant first ∧
          evalMapped (RingHom.id ℝ) ((firstMap first).map constant) second =
            evalNestedFraction constant first second ∧
          (SignType.sign (evalNestedFraction constant first second) : Int) =
            OrderedFn.Infinitesimal.sign (OrderedFn.Infinitesimal.sign OrderedFn.orderSign) constant ∧
          (evalNestedFraction constant first second = 0 ↔ constant = 0) := by
  dsimp only
  letI : Lean.Grind.Field Rat := Field.toGrindField
  let data := Native.nestedEvidence (F := Rat) (context := ()) Lean.Grind.instFieldRat
    HexRationalFnMathlib.ratField_eq descriptor [query] selected
  refine ⟨Native.nestedEvidence_descriptor _ _ _ _ _,
    Native.nestedEvidence_queries _ _ _ _ _, Native.nestedEvidence_selected _ _ _ _ _, ?_⟩
  obtain ⟨embedded, raw, evidence, signs, values⟩ :=
    nested_embedding (Rat.castHom ℝ) Rat.cast_strictMono data.1 data.2.1 data.2.2
  let constant := embedded.raw.head.coeff 0
  obtain ⟨first, positive, below, second, secondPositive, smaller, target,
      targetRaw, targetEvidence, _, observed, headCoefficients, queryCoefficients, fractions⟩ :=
    exists_nested_selected embedded _ signs {constant} 1 zero_lt_one
  have constantData := fractions constant (Finset.mem_singleton_self constant)
  have bound : constant = (data.1.raw.substitute
      (CoefficientMap.ofHom (HexRationalFnMathlib.mapHom
        (HexRationalFnMathlib.mapHom (Rat.castHom ℝ))))).head.coeff 0 := by
    dsimp only [constant]
    rw [raw]
  exact ⟨first, second, positive, below, secondPositive, smaller, target,
    raw ▸ targetRaw, evidence ▸ targetEvidence,
    raw ▸ headCoefficients, queryCoefficients,
    observed.trans (values.trans (Native.nestedEvidence_values _ _ _ _ _)), bound ▸ constantData⟩

/-- info: 'Hex.RealClosure.Specialize.EmbeddingTests.ordinary_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.EmbeddingTests.ordinary_selected

end Hex.RealClosure.Specialize.EmbeddingTests
