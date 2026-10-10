/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.CompletionProducer
public import HexSignDet.ThomOrder
public import TauCeti.Algebra.Polynomial.Thom
public import TauCeti.FieldTheory.RealClosure.AbstractRolle

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

section Word

variable {E : Type u} {K : Type v} {Ctx : Type w}
variable [Zero E] [DecidableEq E] [NatCast E] [Mul E]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))

private theorem sign_int_inj {a b : SignType} (h : (a : Int) = (b : Int)) : a = b := by
  cases a <;> cases b <;> simp_all [SignType.cast]

private theorem sign_int_lt {a b : SignType} (h : a < b) : (a : Int) < (b : Int) := by
  cases a <;> cases b <;> revert h <;> decide

include hm hnat in
/-- The full word reconstructed by the actual descriptor code uniquely
identifies a root. Tau Ceti supplies Thom injectivity and polynomial Rolle
from the real-closed-field axioms, including over non-Archimedean fields. -/
theorem RawDescriptor.full_unique (raw : RawDescriptor E Ctx)
    (hp : interpret f hz raw.head ≠ 0) (x y : K)
    (hx : (interpret f hz raw.head).eval x = 0)
    (hy : (interpret f hz raw.head).eval y = 0)
    (hword : signsAt f hz (raw.full []).queries x =
      signsAt f hz (raw.full []).queries y) : x = y := by
  apply Polynomial.thomEncoding_injOn (interpret f hz raw.head)
    TauCeti.RealClosure.polynomialRolle_of_isRealClosed hp hx hy
  funext i
  have hi : i.val < raw.head.natDegree := by
    simpa only [natDegree_interpret] using i.isLt
  have hget := congrArg (fun word : List Int => word[i.val]?) hword
  rw [raw.full_at f hz hm hnat x, raw.full_at f hz hm hnat y] at hget
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.some.injEq] at hget
  simp only [Polynomial.thomEncoding_def]
  exact sign_int_inj hget

include hm hnat in
/-- Every realized full derivative word has one root in a finite root set.
This supplies the count-one premise needed by actual root-list extraction. -/
theorem RawDescriptor.full_fiber (raw : RawDescriptor E Ctx)
    (hp : interpret f hz raw.head ≠ 0) (roots : Finset K)
    (hroots : ∀ z ∈ roots, (interpret f hz raw.head).eval z = 0)
    (x : K) (hx : x ∈ roots) :
    roots.filter (fun y => signsAt f hz (raw.full []).queries y =
      signsAt f hz (raw.full []).queries x) = {x} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hx, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨hy, hword⟩ := Finset.mem_filter.mp hy
  exact raw.full_unique f hz hm hnat hp y x (hroots y hy) (hroots x hx) hword

include hm hnat in
/-- The actual highest-first comparison of reconstructed full words returns
`lt` for roots in increasing mathematical order. Tau Ceti supplies the last
sign disagreement and the orientation determined by the next common sign. -/
theorem RawDescriptor.full_lt (raw : RawDescriptor E Ctx)
    (hp : interpret f hz raw.head ≠ 0) (x y : K)
    (hx : (interpret f hz raw.head).eval x = 0)
    (hy : (interpret f hz raw.head).eval y = 0) (hxy : x < y) :
    Thom.compareFrom (signsAt f hz (raw.full []).queries x)
      (signsAt f hz (raw.full []).queries y) = some .lt := by
  let p := interpret f hz raw.head
  have hrolle : TauCeti.PolynomialRolle K := TauCeti.RealClosure.polynomialRolle_of_isRealClosed
  have henc : p.thomEncoding x ≠ p.thomEncoding y := by
    intro h
    exact hxy.ne (Polynomial.thomEncoding_injOn p hrolle hp hx hy h)
  obtain ⟨k, hkpos, hkdeg, hne, htail⟩ := Polynomial.exists_derivativeSign_ne p henc
  have hk : k < raw.head.natDegree := by
    simpa only [p, natDegree_interpret] using hkdeg
  let word (z : K) : List Int := (List.range raw.head.natDegree).map
    (fun j => (p.derivativeSign z (j + 1) : Int))
  have hw (z : K) : signsAt f hz (raw.full []).queries z = word z := by
    rw [raw.full_at f hz hm hnat z]
    simp only [word, p, Polynomial.derivativeSign_def]
  rw [hw x, hw y]
  have hlen : (word x).length = (word y).length := by simp only [word, List.length_map]
  have hi : k - 1 < (word x).length := by
    simp only [word, List.length_map, List.length_range]
    omega
  have ht : (word x).drop k = (word y).drop k := by
    apply List.ext_getElem
    · simp only [word, List.length_drop, List.length_map]
    · intro j _ _
      simp only [word, List.getElem_drop, List.getElem_map, List.getElem_range]
      exact congrArg (fun s : SignType => (s : Int)) (htail (k + j + 1) (by omega))
  apply Thom.compareFrom_at_lt (word x) (word y) (k - 1) hlen hi
    (by simpa only [Nat.sub_add_cancel hkpos] using ht)
  rcases (Polynomial.lt_iff_derivativeSign p hrolle hne htail).mp hxy with
    ⟨hsign, hlt⟩ | ⟨hsign, hlt⟩
  · left
    constructor
    · simp only [Nat.sub_add_cancel hkpos, List.head?_drop, word, List.getElem?_map,
        List.getElem?_range hk, Option.map_some, hsign, SignType.coe_one]
    · simpa only [word, List.getElem_map, List.getElem_range, Nat.sub_add_cancel hkpos]
        using sign_int_lt hlt
  · right
    constructor
    · simp only [Nat.sub_add_cancel hkpos, List.head?_drop, word, List.getElem?_map,
        List.getElem?_range hk, Option.map_some, hsign, SignType.coe_neg_one]
    · simpa only [word, List.getElem_map, List.getElem_range, Nat.sub_add_cancel hkpos]
        using sign_int_lt hlt

include hm hnat in
/-- The reconstructed full words always compare, with exactly the mathematical
order of their roots. No successful-comparison premise is required. -/
theorem RawDescriptor.full_order (raw : RawDescriptor E Ctx)
    (hp : interpret f hz raw.head ≠ 0) (x y : K)
    (hx : (interpret f hz raw.head).eval x = 0)
    (hy : (interpret f hz raw.head).eval y = 0) :
    Thom.compareFrom (signsAt f hz (raw.full []).queries x)
      (signsAt f hz (raw.full []).queries y) =
        some (if x < y then .lt else if y < x then .gt else .eq) := by
  by_cases hxy : x < y
  · simpa only [hxy, ↓reduceIte] using raw.full_lt f hz hm hnat hp x y hx hy hxy
  · by_cases hyx : y < x
    · have h := Thom.compareFrom_swap (signsAt f hz (raw.full []).queries y)
        (signsAt f hz (raw.full []).queries x)
      rw [raw.full_lt f hz hm hnat hp y x hy hx hyx] at h
      simpa only [Option.map_some, Ordering.swap, hxy, hyx, ↓reduceIte] using h.symm
    · have he : x = y := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      subst y
      simp only [Thom.compareFrom_self, lt_self_iff_false, ↓reduceIte]

include hm hnat in
/-- Acceptance of the finite strict rule is equivalent to the order of roots. -/
theorem RawDescriptor.full_lt_iff (raw : RawDescriptor E Ctx)
    (hp : interpret f hz raw.head ≠ 0) (x y : K)
    (hx : (interpret f hz raw.head).eval x = 0)
    (hy : (interpret f hz raw.head).eval y = 0) :
    Thom.compareFrom (signsAt f hz (raw.full []).queries x)
      (signsAt f hz (raw.full []).queries y) = some .lt ↔ x < y := by
  rw [raw.full_order f hz hm hnat hp x y hx hy]
  by_cases hxy : x < y
  · simp [hxy]
  · by_cases hyx : y < x <;> simp [hxy, hyx]

end Word

section Selected

variable {E : Type u} {K : Type v} {Ctx : Type w}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hsign in
/-- A validated full descriptor stores exactly the reconstructed word at its
selected mathematical root. The applicability premise retains every slot. -/
theorem Descriptor.full_signs {context : Ctx} (d : Descriptor E Ctx sign context)
    (hfull : d.raw.indices = (List.range d.raw.head.natDegree).map (· + 1)) :
    d.raw.signs = signsAt f hz (d.raw.full []).queries
      (d.root f hz h1 ha hs hm hnat hsign) := by
  have hqueries : d.raw.queries = (d.raw.full []).queries := by
    simp only [RawDescriptor.queries, RawDescriptor.full, hfull]
  rw [← hqueries]
  exact (d.root_spec f hz h1 ha hs hm hnat hsign).2.symm

include h1 ha hs hm hnat hsign in
/-- Applicable full descriptors always compare, and the actual guarded
comparison returns the mathematical order of the selected roots. -/
theorem Descriptor.fullOrder_root {context : Ctx}
    (left right : Descriptor E Ctx sign context)
    (hhead : left.raw.head = right.raw.head)
    (hleft : left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1))
    (hright : right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1)) :
    left.fullOrder right = some
      (if left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign then .lt
       else if right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign
         then .gt else .eq) := by
  let x := left.root f hz h1 ha hs hm hnat hsign
  let y := right.root f hz h1 ha hs hm hnat hsign
  have hx : (interpret f hz left.raw.head).eval x = 0 :=
    (Polynomial.isRoot_of_mem_roots
      ((Tarski.mem_rootsIn _ _ _ x).mp (left.root_spec f hz h1 ha hs hm hnat hsign).1).1).eq_zero
  have hy : (interpret f hz left.raw.head).eval y = 0 := by
    rw [hhead]
    exact (Polynomial.isRoot_of_mem_roots
      ((Tarski.mem_rootsIn _ _ _ y).mp (right.root_spec f hz h1 ha hs hm hnat hsign).1).1).eq_zero
  have hqueries : (right.raw.full []).queries = (left.raw.full []).queries := by
    simp only [RawDescriptor.queries, RawDescriptor.full, hhead]
  have hl := (RawDescriptor.check_eq left.accepted).1
  have hr := (RawDescriptor.check_eq right.accepted).1
  simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hl hr
  have hlenLeft : 0 < left.raw.signs.length := by
    rw [← hl.1.1.1.2, hleft, List.length_map, List.length_range]
    exact hl.1.1.1.1
  have hlenRight : 0 < right.raw.signs.length := by
    rw [← hr.1.1.1.2, hright, List.length_map, List.length_range]
    exact hr.1.1.1.1
  have hemptyLeft : left.raw.signs.isEmpty = false := by
    cases h : left.raw.signs with
    | nil => rw [h] at hlenLeft; contradiction
    | cons a as => rfl
  have hemptyRight : right.raw.signs.isEmpty = false := by
    cases h : right.raw.signs with
    | nil => rw [h] at hlenRight; contradiction
    | cons a as => rfl
  unfold Descriptor.fullOrder
  rw [ite_eq_left ⟨hhead, hleft, hright⟩]
  simp only [Thom.compareSigns, hemptyLeft, hemptyRight, hl.2, hr.2,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  rw [left.full_signs f hz h1 ha hs hm hnat hsign hleft,
    right.full_signs f hz h1 ha hs hm hnat hsign hright, hqueries]
  exact left.raw.full_order f hz hm hnat (left.head_ne_zero f hz) x y hx hy

include h1 ha hs hm hnat hsign in
/-- Every checked cross-polynomial comparison returns the mathematical order
of the original roots. Both full encodings retain the common literal head and
their re-encoding proofs identify their roots with the original selections. -/
theorem Comparison.order_root {context : Ctx}
    {left right : Descriptor E Ctx sign context} (c : Comparison left right) :
    c.order =
      (if left.root f hz h1 ha hs hm hnat hsign < right.root f hz h1 ha hs hm hnat hsign then .lt
       else if right.root f hz h1 ha hs hm hnat hsign < left.root f hz h1 ha hs hm hnat hsign
         then .gt else .eq) := by
  obtain ⟨hguard, _⟩ := Descriptor.fullOrder_eq c.ordered
  have h := c.leftEncoding.target.fullOrder_root f hz h1 ha hs hm hnat hsign
    c.rightEncoding.target hguard.1 hguard.2.1 hguard.2.2
  rw [c.ordered, c.leftEncoding.root_eq_source f hz h1 ha hs hm hnat hsign,
    c.rightEncoding.root_eq_source f hz h1 ha hs hm hnat hsign] at h
  exact Option.some.inj h

end Selected

end Hex.SignDet
