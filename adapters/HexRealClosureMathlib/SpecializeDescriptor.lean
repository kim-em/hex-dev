/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeSelected
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F]

private theorem regular_derivative (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F))
    (regular : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    ∀ i, Regular embedding t (p.derivative.coeff i) := by
  classical
  obtain ⟨P, lift⟩ := polynomial_lift embedding t p regular
  have derivative : P.derivative.map (regularRing embedding t).subtype =
      HexPolyMathlib.toPolynomial p.derivative := by
    rw [← Polynomial.derivative_map, lift, HexPolyMathlib.toPolynomial_derivative]
  intro i
  have coefficient := congrArg (fun q => q.coeff i) derivative
  simp only [Polynomial.coeff_map, HexPolyMathlib.coeff_toPolynomial] at coefficient
  change (P.derivative.coeff i).val = p.derivative.coeff i at coefficient
  rw [← coefficient]
  exact (P.derivative.coeff i).property

/-- The actual derivative sequence specializes from the original coefficient
guards alone. Iterated derivatives stay in the regular coefficient ring. -/
theorem derivativesFrom_specialize (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F)) (n : Nat)
    (regular : ∀ i < p.size, Regular embedding t (p.coeff i)) :
    (Hex.SignDet.derivativesFrom p n).map (fun q => polynomial embedding q t) =
      Hex.SignDet.derivativesFrom (polynomial embedding p t) n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [Hex.SignDet.derivativesFrom, List.map_cons]
    apply congrArg₂ List.cons (polynomial_derivative embedding t p regular)
    rw [ih p.derivative (fun i _ => regular_derivative embedding t p regular i),
      polynomial_derivative embedding t p regular]

/-- Preserving the head's finite zero pattern also preserves the derivative
sequence length selected by its actual degree. -/
theorem derivatives_specialize (embedding : F →+* ℝ) (t : ℝ)
    (p : Hex.DensePoly (Hex.RationalFn F))
    (regular : ∀ i < p.size, Regular embedding t (p.coeff i))
    (reflects : ∀ i < p.size, evalMapped embedding (p.coeff i) t = 0 ↔ p.coeff i = 0) :
    (Hex.SignDet.derivatives p).map (fun q => polynomial embedding q t) =
      Hex.SignDet.derivatives (polynomial embedding p t) := by
  rw [Hex.SignDet.derivatives, Hex.SignDet.derivatives, polynomial_degree embedding p t reflects]
  exact derivativesFrom_specialize embedding t p p.natDegree regular

end Hex.RealClosure.Specialize

namespace Hex.SignDet.RawDescriptor
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u}

/-- Substitute the stored head and endpoints, retaining context, derivative
indices and signs. Queries are recomputed from the specialized head. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (raw : RawDescriptor (RationalFn F) Ctx) : RawDescriptor ℝ Ctx := by
  classical
  exact {
    context := raw.context
    head := polynomial embedding raw.head t
    lower := raw.lower.specialize embedding t
    upper := raw.upper.specialize embedding t
    indices := raw.indices
    signs := raw.signs }

/-- Literal derivative indices and sign guards remain well formed when the
head's actual degree is preserved. -/
theorem wellFormed_specialize (embedding : F →+* ℝ) (t : ℝ)
    (raw : RawDescriptor (RationalFn F) Ctx)
    (reflects : ∀ i < raw.head.size,
      evalMapped embedding (raw.head.coeff i) t = 0 ↔ raw.head.coeff i = 0) :
    (raw.specialize embedding t).wellFormed = raw.wellFormed := by
  classical
  simp only [wellFormed, specialize, polynomial_degree embedding raw.head t reflects]
  rfl

/-- Recomputed formal derivative queries equal substitution of the original
ordered query list, including default zero reads at malformed indices. -/
theorem queries_specialize (embedding : F →+* ℝ) (t : ℝ)
    (raw : RawDescriptor (RationalFn F) Ctx)
    (regular : ∀ i < raw.head.size, Regular embedding t (raw.head.coeff i))
    (reflects : ∀ i < raw.head.size,
      evalMapped embedding (raw.head.coeff i) t = 0 ↔ raw.head.coeff i = 0) :
    (raw.specialize embedding t).queries =
      raw.queries.map (fun q => polynomial embedding q t) := by
  classical
  simp only [queries, specialize, List.map_map]
  rw [← derivatives_specialize embedding t raw.head regular reflects]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, List.getElem?_map]
  cases h : (derivatives raw.head)[i - 1]? with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    exact ((polynomial_zero embedding (0 : DensePoly (RationalFn F)) t (by simp)).mpr rfl).symm
  | some q => simp only [Option.map_some, Option.getD_some]

/-- Finite descriptor data include the head's coefficient array as well as
the full replay inventory for its actual reconstructed derivative queries. -/
@[expose] noncomputable def fractions (raw : RawDescriptor (RationalFn F) Ctx)
    (evidence : Replay (RationalFn F) Ctx) : Finset (RationalFn F) := by
  classical
  exact raw.head.toArray.toList.toFinset ∪
    evidence.fractions raw.head raw.lower raw.upper raw.queries

/-- The complete descriptor checker remains accepted with queries rebuilt
from the specialized head and the same literal count-one replay. -/
theorem check_specialize [DecidableEq Ctx] (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (context : Ctx)
    (raw : RawDescriptor (RationalFn F) Ctx) (evidence : Replay (RationalFn F) Ctx)
    (data : ∀ x ∈ raw.fractions evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x)
    (accepted : raw.check sign context evidence = true) :
    (raw.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int)) context
      (evidence.specialize embedding t) = true := by
  classical
  have head_data (i : Nat) (hi : i < raw.head.size) :=
    data (raw.head.coeff i) (Finset.mem_union_left _
      (List.mem_toFinset.mpr (coefficient_mem raw.head i hi)))
  have regular := fun i hi => (head_data i hi).1
  have reflects := fun i hi => (head_data i hi).2.1
  obtain ⟨wellFormed, bound, replay, one⟩ := check_eq accepted
  have checked : (evidence.specialize embedding t).check (fun x : ℝ => (SignType.sign x : Int))
      context (raw.specialize embedding t).head (raw.specialize embedding t).lower
      (raw.specialize embedding t).upper (raw.specialize embedding t).queries = true := by
    rw [queries_specialize embedding t raw regular reflects]
    exact evidence.check_specialize embedding t sign context raw.head raw.lower raw.upper raw.queries
      (fun x hx => data x (Finset.mem_union_right _ hx)) replay
  simp only [check, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨(wellFormed_specialize embedding t raw reflects).trans wellFormed, bound⟩, checked⟩, ?_⟩
  rw [Replay.node_specialize]
  change evidence.node.system.count raw.signs = 1
  exact (evidence.table_lookup replay raw.signs).symm.trans one

end Hex.SignDet.RawDescriptor

namespace Hex.SignDet.Descriptor
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] {Ctx : Type u} [DecidableEq Ctx]
variable {sign : RationalFn F → Int} {context : Ctx}

/-- Reuse the specialized count-one evidence to construct a checked ordinary
real descriptor whose derivative queries come from its actual new head. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (d : Descriptor (RationalFn F) Ctx sign context)
    (data : ∀ x ∈ d.raw.fractions d.evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    Descriptor ℝ Ctx (fun x : ℝ => (SignType.sign x : Int)) context := by
  classical
  have accepted := d.raw.check_specialize embedding t sign context d.evidence data d.accepted
  simp only [RawDescriptor.check, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ofTable (d.raw.specialize embedding t) (d.evidence.specialize embedding t)
    accepted.1.1.1 accepted.1.1.2 accepted.1.2
    (((d.evidence.specialize embedding t).table_lookup accepted.1.2
      (d.raw.specialize embedding t).signs).trans accepted.2)

/-- The validated result retains the literal specialized raw descriptor. -/
theorem specialize_raw (embedding : F →+* ℝ) (t : ℝ)
    (d : Descriptor (RationalFn F) Ctx sign context)
    (data : ∀ x ∈ d.raw.fractions d.evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    (d.specialize embedding t data).raw = d.raw.specialize embedding t := by
  simp only [specialize, ofTable_raw]

/-- Checking the exact mapped raw input and replay returns this descriptor.
This uses the constructor's public equation across the module boundary. -/
theorem specialize_checked (embedding : F →+* ℝ) (t : ℝ)
    (d : Descriptor (RationalFn F) Ctx sign context)
    (data : ∀ x ∈ d.raw.fractions d.evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    ofReplay? (fun x : ℝ => (SignType.sign x : Int)) context
      (d.raw.specialize embedding t) (d.evidence.specialize embedding t) =
      some (d.specialize embedding t data) := by
  simp only [specialize]
  apply ofReplay_ofTable

/-- The validated descriptor retains the entire literal mapped replay. -/
theorem specialize_evidence (embedding : F →+* ℝ) (t : ℝ)
    (d : Descriptor (RationalFn F) Ctx sign context)
    (data : ∀ x ∈ d.raw.fractions d.evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) = sign x) :
    (d.specialize embedding t data).evidence = d.evidence.specialize embedding t := by
  have accepted := d.raw.check_specialize embedding t sign context d.evidence data d.accepted
  have fields := ofReplay_data (fun x : ℝ => (SignType.sign x : Int)) context
    (d.raw.specialize embedding t) (d.evidence.specialize embedding t)
  rw [specialize_checked embedding t d data, Option.map_some, ite_eq_left accepted] at fields
  exact (Prod.mk.inj (Option.some.inj fields)).2

variable [LinearOrder F] [IsStrictOrderedRing F]

/-- Every parameter in one positive neighborhood gives a validated ordinary
real descriptor returned by checking the mapped evidence and recomputed
formal derivatives. No new sign determination is run. -/
theorem specialize_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (d : Descriptor (RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      ∃ target : Descriptor ℝ Ctx (fun x : ℝ => (SignType.sign x : Int)) context,
        target.raw = d.raw.specialize embedding t ∧
        target.evidence = d.evidence.specialize embedding t ∧
        ofReplay? (fun x : ℝ => (SignType.sign x : Int)) context
          (d.raw.specialize embedding t) (d.evidence.specialize embedding t) = some target ∧
        target.raw.queries = d.raw.queries.map (fun q => polynomial embedding q t) := by
  classical
  obtain ⟨η, positive, signs⟩ := finite_fractions_map embedding ordered (d.raw.fractions d.evidence)
  refine ⟨η, positive, fun t ht small => ?_⟩
  have data : ∀ x ∈ d.raw.fractions d.evidence,
      Regular embedding t x ∧ (evalMapped embedding x t = 0 ↔ x = 0) ∧
      (SignType.sign (evalMapped embedding x t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign x := by
    intro x hx
    have preserved := signs t ht small x hx
    exact ⟨preserved.1, fraction_zero embedding x t preserved.2, preserved.2⟩
  refine ⟨d.specialize embedding t data, specialize_raw embedding t d data,
    specialize_evidence embedding t d data, specialize_checked embedding t d data, ?_⟩
  rw [specialize_raw]
  apply RawDescriptor.queries_specialize
  · intro i hi
    exact (data (d.raw.head.coeff i) (Finset.mem_union_left _
      (List.mem_toFinset.mpr (coefficient_mem d.raw.head i hi)))).1
  · intro i hi
    exact (data (d.raw.head.coeff i) (Finset.mem_union_left _
      (List.mem_toFinset.mpr (coefficient_mem d.raw.head i hi)))).2.1

end Hex.SignDet.Descriptor

namespace Hex.RealClosure.Specialize
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret
attribute [local instance 2000] Field.toGrindField
variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}

/-- All signs from checked selected-sign evidence hold at the root of an
actual validated specialized descriptor. Its formal derivative queries are
recomputed from its new head, rather than supplied as an unrelated prefix. -/
theorem selected_root_near (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context)
    (qs : List (Hex.DensePoly (Hex.RationalFn F))) (s : SelectedSigns d qs) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      ∃ target : Descriptor ℝ Ctx (fun x : ℝ => (SignType.sign x : Int)) context,
        target.raw = d.raw.specialize embedding t ∧
        target.evidence = d.evidence.specialize embedding t ∧
        Descriptor.ofReplay? (fun x : ℝ => (SignType.sign x : Int)) context
          (d.raw.specialize embedding t) (d.evidence.specialize embedding t) = some target ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (qs.map (fun q => polynomial embedding q t))
          (target.root (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ => rfl) (fun _ => rfl)) = s.values.toList := by
  classical
  obtain ⟨η₁, positive₁, descriptors⟩ := d.specialize_near embedding ordered
  obtain ⟨η₂, positive₂, realize⟩ := selected_near embedding ordered d qs s
  refine ⟨min η₁ η₂, lt_min positive₁ positive₂, fun t ht small => ?_⟩
  obtain ⟨target, raw, evidence, checked, queries⟩ := descriptors t ht
    (lt_of_lt_of_le small (min_le_left _ _))
  obtain ⟨x, member, first, rest, unique⟩ := realize t ht
    (lt_of_lt_of_le small (min_le_right _ _))
  let y := target.root (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  have spec := target.root_spec (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
  have root_member : y ∈ Tarski.rootsIn
      (interpret (fun x : ℝ => x) (fun _ => Iff.rfl) (polynomial embedding d.raw.head t))
      ((d.raw.lower.specialize embedding t).map (fun x : ℝ => x))
      ((d.raw.upper.specialize embedding t).map (fun x : ℝ => x)) := by
    simpa only [raw, RawDescriptor.specialize, y] using spec.1
  have selected : signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
      (d.raw.queries.map (fun q => polynomial embedding q t)) y = d.raw.signs := by
    rw [← queries]
    simpa only [raw, RawDescriptor.specialize, y] using spec.2
  have equal : y = x := unique y root_member selected
  refine ⟨target, raw, evidence, checked, ?_⟩
  change signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
    (qs.map (fun q => polynomial embedding q t)) y = s.values.toList
  rw [equal]
  exact rest

end Hex.RealClosure.Specialize

namespace Hex.RealClosure.Specialize.Native
open Hex.SignDet HexRealRootsMathlib HexPolyMathlib.Interpret
variable {F : Type} [Field F] [DecidableEq F] [LinearOrder F] [IsStrictOrderedRing F]
variable {Ctx : Type u} [DecidableEq Ctx] {context : Ctx}

/-- Transport the entire checked descriptor, query list and selected-sign
certificate through equality of the native coefficient dictionary. -/
def evidence (g : Lean.Grind.Field F) (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    (d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context) →
    (qs : List (Hex.DensePoly (Hex.RationalFn F))) → SelectedSigns d qs →
    letI : Lean.Grind.Field F := Field.toGrindField
    Σ d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context,
      Σ qs : List (Hex.DensePoly (Hex.RationalFn F)), SelectedSigns d qs := by
  cases compatible
  exact fun d qs s => ⟨d, qs, s⟩

omit [IsStrictOrderedRing F] in
/-- Whole-dictionary transport preserves the recorded integer signs literally. -/
theorem evidence_values (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g) :
    letI : Lean.Grind.Field F := g
    ∀ (d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn F))) (s : SelectedSigns d qs),
    let values := s.values.toList
    letI : Lean.Grind.Field F := Field.toGrindField
    (evidence g compatible d qs s).2.2.values.toList = values := by
  cases compatible
  intros
  rfl

/-- Native evidence specialized after whole-dictionary transport has the same
checked real descriptor and selected-root signs as canonical evidence. -/
theorem selected_root_near (g : Lean.Grind.Field F)
    (compatible : Field.toGrindField (K := F) = g)
    (embedding : F →+* ℝ) (ordered : StrictMono embedding) :
    letI : Lean.Grind.Field F := g
    ∀ (d : Descriptor (Hex.RationalFn F) Ctx
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) context)
      (qs : List (Hex.DensePoly (Hex.RationalFn F))) (s : SelectedSigns d qs),
    let values := s.values.toList
    letI : Lean.Grind.Field F := Field.toGrindField
    let data := evidence g compatible d qs s
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η →
      ∃ target : Descriptor ℝ Ctx (fun x : ℝ => (SignType.sign x : Int)) context,
        target.raw = data.1.raw.specialize embedding t ∧
        target.evidence = data.1.evidence.specialize embedding t ∧
        Descriptor.ofReplay? (fun x : ℝ => (SignType.sign x : Int)) context
          (data.1.raw.specialize embedding t) (data.1.evidence.specialize embedding t) =
          some target ∧
        signsAt (fun x : ℝ => x) (fun _ => Iff.rfl)
          (data.2.1.map (fun q => polynomial embedding q t))
          (target.root (fun x : ℝ => x) (fun _ => Iff.rfl) rfl
            (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
            (fun _ => rfl) (fun _ => rfl)) = values := by
  intro d qs s
  have realized := Hex.RealClosure.Specialize.selected_root_near embedding ordered
    (evidence g compatible d qs s).1 (evidence g compatible d qs s).2.1
    (evidence g compatible d qs s).2.2
  simpa only [evidence_values] using realized

end Hex.RealClosure.Specialize.Native

/-- info: 'Hex.RealClosure.Specialize.derivativesFrom_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.derivativesFrom_specialize

/-- info: 'Hex.RealClosure.Specialize.derivatives_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.derivatives_specialize

/-- info: 'Hex.SignDet.RawDescriptor.wellFormed_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.wellFormed_specialize

/-- info: 'Hex.SignDet.RawDescriptor.queries_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.queries_specialize

/-- info: 'Hex.SignDet.RawDescriptor.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.RawDescriptor.check_specialize

/-- info: 'Hex.SignDet.Descriptor.specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.specialize

/-- info: 'Hex.SignDet.Descriptor.specialize_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.specialize_near

/-- info: 'Hex.RealClosure.Specialize.selected_root_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.selected_root_near

/-- info: 'Hex.RealClosure.Specialize.Native.selected_root_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.Native.selected_root_near

/-- info: 'Hex.SignDet.Descriptor.specialize_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.specialize_evidence
