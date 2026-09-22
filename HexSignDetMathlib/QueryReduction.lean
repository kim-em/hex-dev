/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.QueryReduction
public import HexSignDet.Replay
public import HexSignDetMathlib.ReductionProducer

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0) (h1 : f (1 : E) = 1)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (sign : E → Int) (hpos : ∀ a, sign a = 1 ↔ 0 < f a)

include h1 ha hs hm hpos in
/-- Arbitrary accepted query preprocessing preserves every indexed sign at
every root, including zeros and duplicate queries. -/
theorem QueryReduction.checkFrom_signs (p : DensePoly E) (qs : List (DensePoly E))
    (steps : List (ReductionStep E)) (i : Nat)
    (h : checkFrom sign p i qs steps = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    (steps.map fun s => SignType.sign ((interpret f hz s.next).eval a)) =
      qs.map (fun q => SignType.sign ((interpret f hz q).eval a)) := by
  induction qs generalizing steps i with
  | nil => cases steps <;> simp_all [checkFrom]
  | cons q qs ih =>
    cases steps with
    | nil => simp [checkFrom] at h
    | cons s ss =>
      have hh : s.check sign p 1 q i = true ∧ checkFrom sign p (i + 1) qs ss = true := by
        simpa only [checkFrom, Bool.and_eq_true] using h
      have he := ReductionStep.check_sign f hz ha hs hm sign hpos p 1 q i s hh.1 a hp
      simp only [interpret_one f hz h1, Polynomial.eval_one, sign_one, one_mul] at he
      simp only [List.map_cons, he, ih ss (i + 1) hh.2]

include h1 ha hs hm hpos in
theorem QueryReduction.check_signs (p : DensePoly E) (qs : List (DensePoly E))
    (r : QueryReduction E) (h : r.check sign p qs = true)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    (r.queries.map fun q => SignType.sign ((interpret f hz q).eval a)) =
      qs.map (fun q => SignType.sign ((interpret f hz q).eval a)) := by
  simp only [check, Bool.and_eq_true] at h
  simpa only [queries, List.map_map, Function.comp_def] using
    checkFrom_signs f hz h1 ha hs hm sign hpos p qs r.steps 0 h.2 a hp

include h1 ha hs hm hpos in
/-- Every checked node's actual Tarski operand has the sign of the original
moment. This composes arbitrary query preprocessing and moment reductions;
neither witness is assumed to have come from the producer. -/
theorem Node.check_sign {Ctx : Type w} [DecidableEq Ctx] [NatCast E]
    (context : Ctx) (p : DensePoly E) (lo hi : Endpoint E)
    (qs : List (DensePoly E)) (n : Node E Ctx)
    (h : n.check sign context p lo hi qs = true) (i : Fin n.size)
    (a : K) (hp : (interpret f hz p).eval a = 0) :
    SignType.sign ((interpret f hz (queryPoly (QueryReduction.operands qs n.preparation)
      n.system.rows[i] n.reductions[i])).eval a) =
      SignType.sign ((interpret f hz (moment qs n.system.rows[i])).eval a) := by
  rw [checkMoment_sign f hz ha hs hm sign hpos h1 context p lo hi _ _ _ _ _
    (Node.check_moment h i) a hp]
  apply moment_congr f hz ha hm h1
  have hc := Node.check_preparation h
  cases he : n.preparation with
  | none => rfl
  | some r =>
    simp only [he] at hc
    exact QueryReduction.check_signs f hz h1 ha hs hm sign hpos p qs r hc a hp

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hneg : ∀ a, sign a < 0 ↔ f a < 0)

include hz h1 ha hs hm hpos hn hi hneg in
/-- The actual query preprocessing producer supplies accepted indexed
evidence without an injectivity assumption on the representation. -/
theorem QueryReduction.buildFrom_checks (p : DensePoly E) (qs : List (DensePoly E))
    (i : Nat) (hp : p ≠ 0) :
    checkFrom sign p i qs (buildFrom sign p i qs) = true := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih =>
    simp only [buildFrom, checkFrom, Bool.and_eq_true]
    exact ⟨ReductionStep.build_checks f hz h1 ha hs hm hn hi sign hpos hneg p 1 q i hp,
      ih (i + 1)⟩

include hz h1 ha hs hm hpos hn hi hneg in
theorem QueryReduction.build_checks (p : DensePoly E) (qs : List (DensePoly E))
    (hp : 0 < p.natDegree) : (build sign p qs).check sign p qs = true := by
  have hpne : p ≠ 0 := by intro hz; simp [hz] at hp
  simp only [build, check, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp, buildFrom_checks f hz h1 ha hs hm sign hpos hn hi hneg p qs 0 hpne⟩

end Hex.SignDet
