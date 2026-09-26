/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootModel
public import HexSignDetMathlib.TreeSolve

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

end Hex.SignDet
