/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.ThomReencoding
public import HexSignDetTheory.CommonProduct
public import HexSignDetTheory.CompletionProducer

public section

namespace Hex.SignDet

open HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Neg E] [Inv E] [Div E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
variable (hd : ∀ a b, f (a / b) = f a / f b)

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The actual comparison producer succeeds for every pair of validated
roots in one coefficient context. The common head is proved squarefree;
joint re-encoding produces full words, and Tau Ceti Thom order compares them.
No assumed construction result, rational separator or injective coefficient
representation is required. -/
theorem Descriptor.buildComparison_success {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    ∃ c : Comparison left right, left.buildComparison right = .ok c := by
  have domain (d : Descriptor E Ctx sign context) :
      HexSturmTheory.Domain f hz d.raw.head d.raw.lower d.raw.upper := by
    obtain ⟨_, _, hc, _⟩ := RawDescriptor.check_eq d.accepted
    exact d.evidence.check_domain f hz h1 ha hs hm hnat sign hsign
      context d.raw.head d.raw.lower d.raw.upper d.raw.queries hc
  obtain ⟨common, hc, hsq⟩ := CommonProduct.build_squarefree f hz ha hs hm hd context
    left.raw.head right.raw.head (domain left).2.1 (domain right).2.1
  have hdom : HexSturmTheory.Domain f hz common.val.head .negInf .posInf :=
    ⟨hsq.ne_zero, hsq, trivial, trivial, trivial⟩
  have hleft : left.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz common.val.head) .negInf .posInf := by
    apply (Tarski.mem_rootsIn_iff _ hsq.ne_zero _ _ _).mpr
    refine ⟨?_, Tarski.inInterval_univ _⟩
    apply (common.val.check_roots f hz ha hs hm common.property _).mpr
    exact Or.inl (Polynomial.isRoot_of_mem_roots
      ((Tarski.mem_rootsIn _ _ _ _).mp (left.root_spec f hz h1 ha hs hm hnat hsign).1).1).eq_zero
  have hright : right.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz common.val.head) .negInf .posInf := by
    apply (Tarski.mem_rootsIn_iff _ hsq.ne_zero _ _ _).mpr
    refine ⟨?_, Tarski.inInterval_univ _⟩
    apply (common.val.check_roots f hz ha hs hm common.property _).mpr
    exact Or.inr (Polynomial.isRoot_of_mem_roots
      ((Tarski.mem_rootsIn _ _ _ _).mp (right.root_spec f hz h1 ha hs hm hnat hsign).1).1).eq_zero
  obtain ⟨l, hl, _⟩ := left.buildReencoding_success f hz h1 ha hs hm hnat hsign hn hi
    common.val.head .negInf .posInf hdom hleft
  obtain ⟨r, hr, _⟩ := right.buildReencoding_success f hz h1 ha hs hm hnat hsign hn hi
    common.val.head .negInf .posInf hdom hright
  have hhead : l.target.raw.head = r.target.raw.head :=
    l.check_eq.1.1.trans r.check_eq.1.1.symm
  have ho := l.target.fullOrder_root f hz h1 ha hs hm hnat hsign r.target hhead
    (left.buildReencoding_full common.val.head .negInf .posInf l hl)
    (right.buildReencoding_full common.val.head .negInf .posInf r hr)
  exact ⟨⟨common.val, common.property, l, r, _, ho⟩,
    left.buildComparison_of_success right common hc l r hl hr _ ho⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The actual order constructor succeeds and agrees with the original roots.
Equal stored heads use two completions directly, even across distinct intervals;
other heads use the checked common-polynomial construction. -/
theorem Descriptor.buildOrder_roots {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    ∃ order, left.buildOrder right = .ok order ∧ order =
      (if left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign then .lt
       else if right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign
         then .gt else .eq) := by
  by_cases hh : left.raw.head = right.raw.head
  · obtain ⟨l, hl⟩ := left.buildCompletion_success f hz h1 ha hs hm hnat hsign hn hi
    obtain ⟨r, hr⟩ := right.buildCompletion_success f hz h1 ha hs hm hnat hsign hn hi
    have hhead := l.bindings.2.1.trans (hh.trans r.bindings.2.1.symm)
    have hlfull : l.descriptor.raw.indices =
        (List.range l.descriptor.raw.head.natDegree).map (· + 1) := by
      rw [l.bindings.2.1]
      exact l.bindings.2.2.2.2.1
    have hrfull : r.descriptor.raw.indices =
        (List.range r.descriptor.raw.head.natDegree).map (· + 1) := by
      rw [r.bindings.2.1]
      exact r.bindings.2.2.2.2.1
    have ho := l.descriptor.fullOrder_root f hz h1 ha hs hm hnat hsign
      r.descriptor hhead hlfull hrfull
    rw [l.root_eq_source f hz h1 ha hs hm hnat hsign,
      r.root_eq_source f hz h1 ha hs hm hnat hsign] at ho
    exact ⟨_, left.buildOrder_ofCompletion right hh l r hl hr _ ho, rfl⟩
  · obtain ⟨c, hc⟩ := left.buildComparison_success f hz h1 ha hs hm hnat hsign hn hi hd right
    exact ⟨c.order, left.buildOrder_ofComparison right hh c hc,
      c.order_root f hz h1 ha hs hm hnat hsign⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The total comparison uses an actual successful order construction;
its internal diagnostic fallback is unreachable under lawful coefficients. -/
theorem Descriptor.compare_success {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    ∃ order, left.buildOrder right = .ok order ∧ left.compare right = order := by
  obtain ⟨order, ho, _⟩ := left.buildOrder_roots f hz h1 ha hs hm hnat hsign hn hi hd right
  exact ⟨order, ho, left.compare_ofBuild right order ho⟩

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- The ordinary total comparison returns precisely the mathematical order
of the original selected roots, including roots of different polynomials. -/
theorem Descriptor.compare_correct {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    left.compare right =
      (if left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign then .lt
       else if right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign
         then .gt else .eq) := by
  obtain ⟨order, ho, hr⟩ := left.buildOrder_roots f hz h1 ha hs hm hnat hsign hn hi hd right
  exact (left.compare_ofBuild right order ho).trans hr

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Equality returned by the total comparison means equality of the selected
roots, including when the stored defining polynomials are different. -/
theorem Descriptor.compare_eq_iff {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    left.compare right = .eq ↔
      left.root f hz h1 ha hs hm hnat hsign = right.root f hz h1 ha hs hm hnat hsign := by
  rw [left.compare_correct f hz h1 ha hs hm hnat hsign hn hi hd right]
  by_cases hxy : left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign
  · simp [hxy, ne_of_lt hxy]
  · by_cases hyx : right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign
    · simp [hxy, hyx, ne_of_gt hyx]
    · have he := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      simp [he]

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Strict increasing order returned by the total comparison is exactly the
strict order of the selected roots. -/
theorem Descriptor.compare_lt_iff {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    left.compare right = .lt ↔
      left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign := by
  rw [left.compare_correct f hz h1 ha hs hm hnat hsign hn hi hd right]
  by_cases hxy : left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign
  · simp [hxy]
  · by_cases hyx : right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign <;>
      simp [hxy, hyx]

include hz h1 ha hs hm hnat hsign hn hi hd in
/-- Strict decreasing order returned by the total comparison is exactly the
reverse strict order of the selected roots. -/
theorem Descriptor.compare_gt_iff {context : Ctx}
    (left right : Descriptor E Ctx sign context) :
    left.compare right = .gt ↔
      right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign := by
  rw [left.compare_correct f hz h1 ha hs hm hnat hsign hn hi hd right]
  by_cases hxy : left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign
  · simp [hxy, lt_asymm hxy]
  · by_cases hyx : right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign <;>
      simp [hxy, hyx]

end Hex.SignDet
