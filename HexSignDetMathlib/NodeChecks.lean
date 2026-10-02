/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.NodeProducer
public import HexSignDetMathlib.QueryReduction
public import HexSturmMathlib.Domain

public section

namespace Hex.SignDet

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0) (h1 : f (1 : E) = 1)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (sign : E → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0)

include hz h1 ha hs hm hn hi hpos hneg in
omit [DecidableEq Ctx] in
/-- The selected query preprocessing is valid before matrix solving. -/
theorem nodePreparation_checks (domain : Sturm.PreparedDomain E)
    (hsign : domain.sign = sign) (qs : List (DensePoly E)) (reduced : Bool)
    (preparation : Option (QueryReduction E))
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true) :
    (match nodePreparation reduced domain qs preparation with
      | none => true | some r => r.check sign domain.head qs) = true := by
  subst sign
  unfold nodePreparation
  by_cases hu : useReduction reduced domain = true
  · simp only [hu, ↓reduceIte]
    cases preparation with
    | some r => exact hp
    | none =>
      apply QueryReduction.build_checks f hz h1 ha hs hm domain.sign hpos hn hi hneg
      simp only [useReduction, Bool.and_eq_true, decide_eq_true_eq] at hu
      exact hu.2
  · simp [hu]

include hz h1 ha hs hm hn hi hpos hneg in
omit [DecidableEq Ctx] in
/-- Node construction either retains the checked supplied preprocessing or
builds valid preprocessing itself. The disabled path carries none. -/
theorem buildNode_preparation (context : Ctx) (domain : Sturm.PreparedDomain E)
    (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) {n : Node E Ctx}
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true)
    (h : buildNode context domain qs rows columns reduced inverse preparation = .ok n) :
    (match n.preparation with | none => true | some r => r.check sign domain.head qs) = true := by
  rw [(buildNode_evidence context domain qs rows columns reduced inverse preparation h).1]
  exact nodePreparation_checks f hz h1 ha hs hm hn hi sign hpos hneg
    domain hsign qs reduced preparation hp

include hz h1 ha hs hm hn hi hpos hneg in
/-- Every successful node passes local replay under the generic coefficient
laws and valid supplied preprocessing. This proves acceptance of the actual
query certificates; it does not interpret their values as root sums. -/
theorem buildNode_checks (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (context : Ctx) (domain : Sturm.PreparedDomain E) (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (rows : List (List Nat)) (columns : List (List Int))
    (reduced : Bool) (inverse : Option (Int × Matrix Int rows.length rows.length))
    (preparation : Option (QueryReduction E)) {n : Node E Ctx}
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true)
    (h : buildNode context domain qs rows columns reduced inverse preparation = .ok n) :
    n.check sign context domain.head domain.lower domain.upper qs = true := by
  subst sign
  obtain ⟨hctx, hhead, hlo, hhi, hqs, _, _, hsys, hb⟩ :=
    buildNode_spec context domain qs rows columns reduced inverse preparation h
  have he := buildNode_evidence context domain qs rows columns reduced inverse preparation h
  have hprep := buildNode_preparation f hz h1 ha hs hm hn hi domain.sign hpos hneg
    context domain rfl qs rows columns reduced inverse preparation hp h
  apply Node.check_of_basis domain.sign context domain.head domain.lower domain.upper qs n
    ⟨hctx, hhead, hlo, hhi, hqs⟩ hsys hb hprep
  intro i
  have hrow : n.system.rows[i].length = qs.length ∧ n.system.rows[i].all (· ≤ 2) = true := by
    have hh := hsys
    simp only [System.check, Bool.and_eq_true] at hh
    have hx := List.all_eq_true.mp hh.1.1.1.1.1 n.system.rows[i]
      (List.getElem_mem (by simp))
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hx
  have hlen : (QueryReduction.operands qs n.preparation).length = qs.length := by
    cases hp : n.preparation with
    | none => rfl
    | some r =>
      simp only [hp] at hprep
      exact (QueryReduction.check_bounds hprep).1
  simp only [checkMoment_eq, Bool.and_eq_true]
  constructor
  · rw [(he.2 i).1]
    unfold nodeReduction
    by_cases hu : useReduction reduced domain = true
    · simp only [hu, ↓reduceIte]
      apply Reduction.build_checks f hz h1 ha hs hm hn hi domain.sign hpos hneg
      · simp only [useReduction, Bool.and_eq_true, decide_eq_true_eq] at hu
        exact hu.2
      · exact hlen.trans hrow.1.symm
      · exact hrow.2
    · simp only [hu, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hlen.trans hrow.1.symm, hrow.2⟩
  · rw [(he.2 i).2.2, (he.2 i).2.1]
    exact HexSturmMathlib.certifyPrepared_checks f hz ha hs hm domain.sign hneg h1 hn hi
      hpos hbound context domain rfl _

end Hex.SignDet
