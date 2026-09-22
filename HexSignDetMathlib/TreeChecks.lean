/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.NodeChecks

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
/-- Every successful recursive construction passes the independent tree
checker, including child evidence and exact Cartesian support bindings.
This is algebraic producer acceptance, not semantic root-sum soundness. -/
theorem buildTreeFrom_checks (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (context : Ctx) (domain : Sturm.PreparedDomain E) (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) (preparation : Option (QueryReduction E))
    {t : Replay E Ctx}
    (hp : (match preparation with | none => true | some r => r.check sign domain.head qs) = true)
    (h : buildTreeFrom context domain qs reduced preparation = .ok t) :
    t.check sign context domain.head domain.lower domain.upper qs = true := by
  rw [buildTreeFrom] at h
  split at h
  · rename_i hsmall
    simp only [bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i n hnode
      cases h
      have hh := buildNode_spec context domain qs (leafRows qs.length) (leafColumns qs.length)
        reduced none preparation hnode
      simp only [Replay.check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hsmall, hh.2.2.2.2.2.2.1⟩, hh.2.2.2.2.2.1⟩,
        buildNode_checks f hz h1 ha hs hm hn hi sign hpos hneg hbound
          context domain hsign qs _ _ reduced none preparation hp hnode⟩
  · rename_i hlarge
    simp only [bind, Except.bind] at h
    split at h
    · contradiction
    · rename_i l hl
      split at h
      · contradiction
      · rename_i r hr
        split at h
        · contradiction
        · rename_i n hnode
          cases h
          have hpl : (match preparation.map (fun r => r.slice 0 (qs.length / 2)) with
              | none => true | some r => r.check sign domain.head (qs.take (qs.length / 2))) = true := by
            cases preparation with
            | none => rfl
            | some prep => simpa using QueryReduction.slice_checks hp 0 (qs.length / 2)
          have hpr : (match preparation.map
                (fun r => r.slice (qs.length / 2) (qs.length - qs.length / 2)) with
              | none => true | some r => r.check sign domain.head (qs.drop (qs.length / 2))) = true := by
            cases preparation with
            | none => rfl
            | some prep =>
              simpa only [Option.map_some, ← List.length_drop, List.take_length] using
                QueryReduction.slice_checks hp (qs.length / 2) (qs.length - qs.length / 2)
          have hleft := buildTreeFrom_checks hbound
            context domain hsign _ reduced _ hpl hl
          have hright := buildTreeFrom_checks hbound
            context domain hsign _ reduced _ hpr hr
          have hh := buildNode_spec context domain qs _ _ reduced _ preparation hnode
          simp only [Replay.check, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨⟨⟨⟨by omega, hleft⟩, hright⟩, hh.2.2.2.2.2.2.1⟩, hh.2.2.2.2.2.1⟩,
            buildNode_checks f hz h1 ha hs hm hn hi sign hpos hneg hbound
              context domain hsign qs _ _ reduced _ preparation hp hnode⟩
termination_by qs.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

include hz h1 ha hs hm hn hi hpos hneg in
/-- Top-level shared preprocessing supplies the recursive check's invariant. -/
theorem buildTree_checks (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (context : Ctx) (domain : Sturm.PreparedDomain E) (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) {t : Replay E Ctx}
    (h : buildTree context domain qs reduced = .ok t) :
    t.check sign context domain.head domain.lower domain.upper qs = true := by
  subst sign
  unfold buildTree at h
  apply buildTreeFrom_checks f hz h1 ha hs hm hn hi domain.sign hpos hneg hbound
    context domain rfl qs reduced _ _ h
  by_cases hu : useReduction reduced domain = true
  · simp only [hu, ↓reduceIte]
    apply QueryReduction.build_checks f hz h1 ha hs hm domain.sign hpos hn hi hneg
    simp only [useReduction, Bool.and_eq_true, decide_eq_true_eq] at hu
    exact hu.2
  · simp [hu]

include hz h1 ha hs hm hn hi hpos hneg in
/-- The final replay guard cannot introduce a diagnostic failure after the
actual tree producer has succeeded. The retained proof checks the same tree. -/
theorem buildPrepared_eq (hbound : ∀ a, -1 ≤ sign a ∧ sign a ≤ 1)
    (context : Ctx) (domain : Sturm.PreparedDomain E) (hsign : domain.sign = sign)
    (qs : List (DensePoly E)) (reduced : Bool) {t : Replay E Ctx}
    (h : buildTree context domain qs reduced = .ok t) :
    ∃ hc, buildPrepared context domain qs reduced = .ok ⟨t, hc⟩ := by
  have hc := buildTree_checks f hz h1 ha hs hm hn hi sign hpos hneg hbound
    context domain hsign qs reduced h
  rw [← hsign] at hc
  refine ⟨hc, ?_⟩
  simp only [buildPrepared, h, bind, Except.bind, hc, ↓reduceDIte]
  rfl

end Hex.SignDet
