/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootModel
public import HexSignDetMathlib.TreeSolve
public import HexSignDetMathlib.Derivatives
public import HexSignDet.Descriptor

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hn hi hsign in
/-- The actual prepared queries compute the moments of the root observations,
including query preprocessing and reduced polynomial products. -/
theorem query_values {Ctx : Type w} (context : Ctx)
    (domain : Sturm.PreparedDomain E) (binding : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true) :
    QueryValues context domain qs reduced preparation
      (rootObservations f hz domain.head qs domain.lower domain.upper) := by
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have hpos := fun x => (hsg x).1
  have hneg := fun x => (hsg x).2.1
  have prep := nodePreparation_checks f hz h1 ha hs hm hn hi sign hpos hneg
    domain binding qs reduced preparation hp
  let pr := nodePreparation reduced domain qs preparation
  let operands := QueryReduction.operands qs pr
  change (match pr with | none => true | some r => r.check sign domain.head qs) = true at prep
  have hlen : operands.length = qs.length := by
    cases he : pr with
    | none => simp [operands, he, QueryReduction.operands]
    | some r =>
      rw [he] at prep
      simpa [operands, he, QueryReduction.operands] using (QueryReduction.check_bounds prep).1
  intro es hes hbound
  have red : (match nodeReduction reduced domain operands es with
      | none => true | some r => r.check sign domain.head operands es) = true := by
    unfold nodeReduction
    by_cases hu : useReduction reduced domain = true
    · simp only [hu, ↓reduceIte]
      rw [binding]
      apply Reduction.build_checks f hz h1 ha hs hm hn hi sign hpos hneg
      · simp only [useReduction, Bool.and_eq_true, decide_eq_true_eq] at hu
        exact hu.2
      · exact hlen.trans hes.symm
      · exact hbound
    · simp [hu]
  rw [Sturm.certifyPrepared_value,
    HexSturmMathlib.queryPrepared_sound f hz h1 ha hs hm hnat sign hsign hn hi domain binding]
  simp only [rootObservations, List.map_map, Function.comp_def, Tarski.rootSum_eq_sum,
    Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro x hx
  have zero : (interpret f hz domain.head).eval x = 0 :=
    Polynomial.isRoot_of_mem_roots ((Tarski.mem_rootsIn _ _ _ x).mp hx).1
  have reduced_sign : SignType.sign ((interpret f hz
      (queryPoly operands es (nodeReduction reduced domain operands es))).eval x) =
      SignType.sign ((interpret f hz (moment operands es)).eval x) := by
    cases he : nodeReduction reduced domain operands es with
    | none => rfl
    | some r =>
      rw [he] at red
      exact Reduction.check_sign f hz ha hs hm sign hpos h1 domain.head operands es r red x zero
  change (SignType.sign ((interpret f hz
    (queryPoly operands es (nodeReduction reduced domain operands es))).eval x) : Int) = _
  rw [reduced_sign]
  have same : SignType.sign ((interpret f hz (moment operands es)).eval x) =
      SignType.sign ((interpret f hz (moment qs es)).eval x) := by
    apply moment_congr f hz ha hm h1
    cases he : pr with
    | none => simp [operands, he, QueryReduction.operands]
    | some r =>
      rw [he] at prep
      simpa [operands, he, QueryReduction.operands] using
        QueryReduction.check_signs f hz h1 ha hs hm sign hpos domain.head qs r prep x zero
  rw [same]
  exact moment_entry f hz ha hm h1 qs es x

include h1 ha hs hm hnat hn hi hsign in
/-- Root moments satisfy the finite producer model at every actual recursive
slice, without a premise about solver success or support completeness. -/
theorem query_model {Ctx : Type w} (context : Ctx)
    (domain : Sturm.PreparedDomain E) (binding : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true) :
    QueryModel context domain qs reduced preparation
      (rootObservations f hz domain.head qs domain.lower domain.upper) := by
  rw [QueryModel]
  refine ⟨query_values f hz h1 ha hs hm hnat hn hi sign hsign context domain binding
    qs reduced preparation hp, ?_⟩
  split
  · trivial
  · have hl : (match preparation.map (fun r => r.slice 0 (qs.length / 2)) with
        | none => true | some r => r.check sign domain.head (qs.take (qs.length / 2))) = true := by
      cases preparation with
      | none => rfl
      | some r => simpa using QueryReduction.slice_checks hp 0 (qs.length / 2)
    have hr : (match preparation.map
          (fun r => r.slice (qs.length / 2) (qs.length - qs.length / 2)) with
        | none => true | some r => r.check sign domain.head (qs.drop (qs.length / 2))) = true := by
      cases preparation with
      | none => rfl
      | some r =>
        simpa only [Option.map_some, ← List.length_drop, List.take_length] using
          QueryReduction.slice_checks hp (qs.length / 2) (qs.length - qs.length / 2)
    constructor
    · simpa only [rootObservations_take] using query_model context domain binding
        (qs.take (qs.length / 2)) reduced _ hl
    · simpa only [rootObservations_drop] using query_model context domain binding
        (qs.drop (qs.length / 2)) reduced _ hr
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

include h1 ha hs hm hnat hn hi hsign in
/-- On a valid prepared domain, actual BKR construction succeeds and counts
the root sign conditions exactly at every node. There is no assumed query
model, successful output, finite support or invertible system in the premises. -/
theorem buildPrepared_roots {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (domain : Sturm.PreparedDomain E) (binding : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) :
    ∃ t, buildPrepared context domain qs reduced = .ok t ∧
      t.val.Counted qs.length (rootObservations f hz domain.head qs domain.lower domain.upper) := by
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have prep := nodePreparation_checks f hz h1 ha hs hm hn hi sign
    (fun x => (hsg x).1) (fun x => (hsg x).2.1) domain binding qs reduced none rfl
  have model := query_model f hz h1 ha hs hm hnat hn hi sign hsign context domain binding
    qs reduced (nodePreparation reduced domain qs none) prep
  obtain ⟨t, ht, counted, _⟩ := buildPrepared_complete f hz h1 ha hs hm hn hi sign
    (fun x => (hsg x).1) (fun x => (hsg x).2.1) (fun x => (hsg x).2.2.2)
    context domain binding qs reduced _ (rootObservations_valid f hz _ _ _ _) model
  exact ⟨t, ht, counted⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- Under a lawful coefficient interpretation, building any raw descriptor
cannot fail with an internal BKR error. -/
theorem Descriptor.build_noError {Ctx : Type w} [DecidableEq Ctx] (context : Ctx)
    (raw : RawDescriptor E Ctx) :
    ∃ result, Descriptor.build sign context raw = .ok result := by
  apply Descriptor.build_ok_ofPrepared sign context raw
  intro domain hd
  have binding := (Sturm.prepare_eq_some sign raw.head raw.lower raw.upper domain hd).1
  obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
    context domain binding raw.queries true
  exact ⟨t, ht⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- With matching context and a prepared domain, a well-formed raw descriptor
realized by exactly one root is accepted by the actual constructor. -/
theorem Descriptor.build_of_unique_root {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx)
    (hctx : raw.context = context) (hw : raw.wellFormed = true)
    (domain : Sturm.PreparedDomain E)
    (hd : Sturm.prepare sign raw.head raw.lower raw.upper = some domain)
    (hone : ((Tarski.rootsIn (interpret f hz raw.head)
      (raw.lower.map f) (raw.upper.map f)).filter
      (fun x => signsAt f hz raw.queries x = raw.signs)).card = 1) :
    ∃ d, Descriptor.build sign context raw = .ok (.ok d) := by
  have bindings := Sturm.prepare_eq_some sign raw.head raw.lower raw.upper domain hd
  obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
    context domain bindings.1 raw.queries true
  have hc : t.val.check sign context raw.head raw.lower raw.upper raw.queries = true := by
    simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
  apply Descriptor.build_ofCount sign context raw hctx domain hd hw t ht
  exact (t.val.count_roots f hz h1 ha hs hm hnat sign hsign context raw.head
    raw.lower raw.upper raw.queries hc raw.signs).trans hone

include hz h1 ha hs hm hnat hn hi hsign in
/-- Descriptor construction succeeds exactly for a valid domain and a
well-formed sign word realized by one root. -/
theorem Descriptor.build_success_iff {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx) :
    (∃ d, Descriptor.build sign context raw = .ok (.ok d)) ↔
      raw.context = context ∧ raw.wellFormed = true ∧
      HexSturmMathlib.Domain f hz raw.head raw.lower raw.upper ∧
      ((Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => signsAt f hz raw.queries x = raw.signs)).card = 1 := by
  constructor
  · rintro ⟨d, hbuild⟩
    have hraw := Descriptor.build_raw hbuild
    obtain ⟨hw, hctx, hc, hcount⟩ := RawDescriptor.check_eq d.accepted
    have hw' : raw.wellFormed = true := by simpa only [hraw] using hw
    have hctx' : raw.context = context := by simpa only [hraw] using hctx
    have hc' : d.evidence.check sign context raw.head raw.lower raw.upper
        raw.queries = true := by simpa only [hraw] using hc
    have hsystem : d.evidence.node.system.count raw.signs = 1 := by
      have hbase := (d.evidence.table_lookup hc d.raw.signs).symm.trans hcount
      simpa only [hraw] using hbase
    refine ⟨hctx', hw', d.evidence.check_domain f hz h1 ha hs hm hnat sign hsign
      context raw.head raw.lower raw.upper raw.queries hc', ?_⟩
    rw [← d.evidence.count_roots f hz h1 ha hs hm hnat sign hsign context
      raw.head raw.lower raw.upper raw.queries hc' raw.signs]
    exact hsystem
  · rintro ⟨hctx, hw, hdom, hone⟩
    have hsg := HexSturmMathlib.sign_spec f sign hsign
    have hp : (Sturm.prepare sign raw.head raw.lower raw.upper).isSome = true :=
      (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
        (fun x => (hsg x).2.1) (fun x => (hsg x).2.2.1)
        h1 hn hi hnat (fun x => (hsg x).1) raw.head raw.lower raw.upper).mpr hdom
    cases hd : Sturm.prepare sign raw.head raw.lower raw.upper with
    | none => simp [hd] at hp
    | some domain =>
      exact Descriptor.build_of_unique_root f hz h1 ha hs hm hnat hn hi sign hsign
        context raw hctx hw domain hd hone

include hz h1 ha hs hm hnat hn hi hsign in
/-- The public validator succeeds exactly for a well-formed raw descriptor
that selects one real root in a valid domain. -/
theorem Descriptor.validate_success_iff {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx) :
    (∃ d, Descriptor.validate sign context raw = some d) ↔
      raw.context = context ∧ raw.wellFormed = true ∧
      HexSturmMathlib.Domain f hz raw.head raw.lower raw.upper ∧
      ((Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => signsAt f hz raw.queries x = raw.signs)).card = 1 := by
  simpa only [Descriptor.validate_eq_some] using
    (Descriptor.build_success_iff f hz h1 ha hs hm hnat hn hi sign hsign context raw)

include hz h1 ha hs hm hnat hn hi hsign in
/-- On a valid raw input, the constructor reports no matching root, one
accepted root, or multiple matching roots according to the exact cardinality. -/
theorem Descriptor.build_valid_cases {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx)
    (hctx : raw.context = context) (hw : raw.wellFormed = true)
    (hdom : HexSturmMathlib.Domain f hz raw.head raw.lower raw.upper) :
    let n := ((Tarski.rootsIn (interpret f hz raw.head)
      (raw.lower.map f) (raw.upper.map f)).filter
      (fun x => signsAt f hz raw.queries x = raw.signs)).card
    (n = 0 ∧ Descriptor.build sign context raw = .ok (.error .absent)) ∨
    (n = 1 ∧ ∃ d, Descriptor.build sign context raw = .ok (.ok d)) ∨
    (1 < n ∧ Descriptor.build sign context raw = .ok (.error .ambiguous)) := by
  dsimp only
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have hp : (Sturm.prepare sign raw.head raw.lower raw.upper).isSome = true :=
    (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
      (fun x => (hsg x).2.1) (fun x => (hsg x).2.2.1)
      h1 hn hi hnat (fun x => (hsg x).1) raw.head raw.lower raw.upper).mpr hdom
  cases hd : Sturm.prepare sign raw.head raw.lower raw.upper with
  | none => simp [hd] at hp
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign raw.head raw.lower raw.upper domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 raw.queries true
    have hc : t.val.check sign context raw.head raw.lower raw.upper raw.queries = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    have hcount := t.val.count_roots f hz h1 ha hs hm hnat sign hsign context
      raw.head raw.lower raw.upper raw.queries hc raw.signs
    by_cases hzero : ((Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => signsAt f hz raw.queries x = raw.signs)).card = 0
    · left
      refine ⟨hzero, ?_⟩
      exact Descriptor.build_absent_ofCount sign context raw hctx domain hd hw t ht
        (hcount.trans hzero)
    · by_cases hone : ((Tarski.rootsIn (interpret f hz raw.head)
          (raw.lower.map f) (raw.upper.map f)).filter
          (fun x => signsAt f hz raw.queries x = raw.signs)).card = 1
      · right; left
        refine ⟨hone, ?_⟩
        exact Descriptor.build_ofCount sign context raw hctx domain hd hw t ht
          (hcount.trans hone)
      · right; right
        have hgt : 1 < ((Tarski.rootsIn (interpret f hz raw.head)
          (raw.lower.map f) (raw.upper.map f)).filter
          (fun x => signsAt f hz raw.queries x = raw.signs)).card := by omega
        refine ⟨hgt, ?_⟩
        exact Descriptor.build_ambiguous_ofCount sign context raw hctx domain hd hw t ht
          (by intro he; exact hone (hcount.symm.trans he))
          (by intro he; exact hzero (hcount.symm.trans he))

include hz h1 ha hs hm hnat hn hi hsign in
/-- The constructor's success criterion expressed with formal iterated
derivatives, as in the abstract validity condition. -/
theorem Descriptor.build_success_formal {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx) :
    (∃ d, Descriptor.build sign context raw = .ok (.ok d)) ↔
      raw.context = context ∧ raw.wellFormed = true ∧
      HexSturmMathlib.Domain f hz raw.head raw.lower raw.upper ∧
      ((Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => raw.indices.map (fun j =>
          (SignType.sign ((Polynomial.derivative^[j]
            (interpret f hz raw.head)).eval x) : Int)) = raw.signs)).card = 1 := by
  rw [Descriptor.build_success_iff f hz h1 ha hs hm hnat hn hi sign hsign context raw]
  have hfilter (hw : raw.wellFormed = true) :
      (Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => signsAt f hz raw.queries x = raw.signs) =
      (Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => raw.indices.map (fun j =>
          (SignType.sign ((Polynomial.derivative^[j]
            (interpret f hz raw.head)).eval x) : Int)) = raw.signs) := by
    apply Finset.filter_congr
    intro x hx
    change raw.queries.map (fun q =>
      (SignType.sign ((interpret f hz q).eval x) : Int)) = raw.signs ↔ _
    rw [raw.querySigns f hz hnat hm hw x]
  constructor
  · rintro ⟨hctx, hw, hdom, hcount⟩
    refine ⟨hctx, hw, hdom, ?_⟩
    simpa only [hfilter hw] using hcount
  · rintro ⟨hctx, hw, hdom, hcount⟩
    refine ⟨hctx, hw, hdom, ?_⟩
    simpa only [hfilter hw] using hcount

include hz h1 ha hs hm hnat hn hi hsign in
/-- Validation succeeds exactly when one real root has the requested formal
derivative signs. -/
theorem Descriptor.validate_success_formal {Ctx : Type w} [DecidableEq Ctx]
    (context : Ctx) (raw : RawDescriptor E Ctx) :
    (∃ d, Descriptor.validate sign context raw = some d) ↔
      raw.context = context ∧ raw.wellFormed = true ∧
      HexSturmMathlib.Domain f hz raw.head raw.lower raw.upper ∧
      ((Tarski.rootsIn (interpret f hz raw.head)
        (raw.lower.map f) (raw.upper.map f)).filter
        (fun x => raw.indices.map (fun j =>
          (SignType.sign ((Polynomial.derivative^[j]
            (interpret f hz raw.head)).eval x) : Int)) = raw.signs)).card = 1 := by
  simpa only [Descriptor.validate_eq_some] using
    (Descriptor.build_success_formal f hz h1 ha hs hm hnat hn hi sign hsign context raw)

end Hex.SignDet
