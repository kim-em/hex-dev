/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Thom
public import HexSignDetMathlib.RootList

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w}
variable [Zero E] [DecidableEq E] [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include hz h1 ha hs hm hnat hsign in
/-- Different realized full words strictly compare. Mathematical totality and
Thom injectivity exclude the diagnostic and equality branches. -/
theorem Descriptor.fullOrder_strict {context : Ctx}
    (left right : Descriptor E Ctx sign context)
    (hhead : left.raw.head = right.raw.head)
    (hleft : left.raw.indices = (List.range left.raw.head.natDegree).map (· + 1))
    (hright : right.raw.indices = (List.range right.raw.head.natDegree).map (· + 1))
    (hne : left.raw.signs ≠ right.raw.signs) :
    left.fullOrder right = some .lt ∨ left.fullOrder right = some .gt := by
  have hroots : left.root f hz h1 ha hs hm hnat hsign ≠
      right.root f hz h1 ha hs hm hnat hsign := by
    intro he
    apply hne
    rw [left.full_signs f hz h1 ha hs hm hnat hsign hleft,
      right.full_signs f hz h1 ha hs hm hnat hsign hright, he]
    have hqueries : (left.raw.full []).queries = (right.raw.full []).queries := by
      simp only [RawDescriptor.queries, RawDescriptor.full, hhead]
    rw [hqueries]
  have ho := left.fullOrder_root f hz h1 ha hs hm hnat hsign right hhead hleft hright
  rcases lt_or_gt_of_ne hroots with hlt | hgt
  · exact Or.inl (by simpa only [hlt, ↓reduceIte] using ho)
  · exact Or.inr (by simpa only [hgt.not_gt, hgt, ↓reduceIte] using ho)

include hz h1 ha hs hm hnat hsign in
/-- The actual shared-table extraction succeeds on distinct count-one full
rows. Mathematical strict totality discharges every insertion guard. The
public producer theorem separately derives these finite table premises. -/
theorem Descriptor.rootsFromTable_success {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    (rows : List (List Int × Nat))
    (hrows : ∀ row ∈ rows, row ∈ (t.table hc).rows.toList)
    (hones : ∀ row ∈ rows, row.2 = 1) (hnd : (rows.map Prod.fst).Nodup) :
    ∃ out, rootsFromTable raw t hp hctx hc rows hrows = .ok out := by
  induction rows with
  | nil => exact ⟨[], rootsFromTable_nil raw t hp hctx hc hrows⟩
  | cons row rows ih =>
    have hone := hones row (by simp)
    have hdistinct := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    let tailMember := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    obtain ⟨rest, hr⟩ := ih tailMember
      (fun r hr => hones r (List.mem_cons_of_mem _ hr)) hdistinct.2
    let d := ofFullRow raw t hp hctx hc row (hrows row (by simp)) hone
    have hdraw : d.raw = raw.full row.1 := ofFullRow_raw _ _ _ _ _ _ _ _
    have hrest := (rootsFromTable_eq raw t hp hctx hc rows tailMember).symm.trans hr
    have hperm := rootsFrom_perm sign context raw t hrest
    have hstrict : ∀ e ∈ rest, d.fullOrder e = some .lt ∨ d.fullOrder e = some .gt := by
      intro e he
      obtain ⟨word, hraw⟩ := rootsFrom_raw sign context raw t hrest e he
      apply d.fullOrder_strict f hz h1 ha hs hm hnat hsign e
      · rw [hdraw, hraw]; rfl
      · rw [hdraw]; rfl
      · rw [hraw]; rfl
      · intro heq
        apply hdistinct.1
        have hmem : e.raw.signs ∈ rows.map Prod.fst :=
          hperm.mem_iff.mp (List.mem_map.mpr ⟨e, he, rfl⟩)
        simpa only [← heq, hdraw, RawDescriptor.full] using hmem
    obtain ⟨out, hout⟩ := Thom.insert_success d rest hstrict
    refine ⟨out, ?_⟩
    rw [rootsFromTable_cons raw t hp hctx hc row rows hrows hone]
    simp only [hr, Except.bind]
    exact hout

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- Actual root enumeration succeeds on every valid domain. Shared query
semantics and Tau Ceti Thom injectivity derive all count-one rows; strict
Thom totality discharges insertion. No output or count premise is assumed. -/
theorem Descriptor.buildRoots_success (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (hdom : HexSturmMathlib.Domain f hz p a b) :
    ∃ out, Descriptor.buildRoots sign context p a b = .ok (some out) := by
  by_cases hconstant : p.natDegree = 0
  · exact ⟨[], Descriptor.buildRoots_constant_success f hz h1 ha hs hm hnat hsign
      hn hi context p a b hdom hconstant⟩
  have hp : 0 < p.natDegree := Nat.pos_of_ne_zero hconstant
  let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
  let roots := Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have hprepared : (Sturm.prepare sign p a b).isSome = true :=
    (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
      (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
      h1 hn hi hnat (fun a => (hsg a).1) p a b).mpr hdom
  cases hd : Sturm.prepare sign p a b with
  | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hprepared
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign p a b domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 (raw.full []).queries true
    have hc : t.val.check sign context p a b (raw.full []).queries = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    let table := t.val.table hc
    have hones : ∀ row ∈ table.rows.toList, row.2 = 1 := by
      intro row hr
      have hcount := table.count_mem hr
      rw [Replay.table_lookup, t.val.count_roots f hz h1 ha hs hm hnat sign hsign
        context p a b (raw.full []).queries hc row.1] at hcount
      have hpositive := (table.wellFormed row hr).2.2
      rw [← hcount] at hpositive
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
      obtain ⟨hx, hword⟩ := Finset.mem_filter.mp hx
      have hfiber := raw.full_fiber f hz hm hnat hdom.1 roots
        (fun z hz => (Polynomial.isRoot_of_mem_roots
          ((Tarski.mem_rootsIn _ _ _ z).mp hz).1).eq_zero) x hx
      rw [← hword, hfiber, Finset.card_singleton] at hcount
      exact hcount.symm
    obtain ⟨out, hout⟩ := rootsFromTable_success f hz h1 ha hs hm hnat hsign
      raw t.val hp rfl hc table.rows.toList (fun _ hr => hr) hones table.distinct
    have hextract := (rootsFromTable_eq raw t.val hp rfl hc table.rows.toList
      (fun _ hr => hr)).symm.trans hout
    have hrows : table.rows.toList = t.val.node.system.tableRows.toList :=
      congrArg Array.toList (t.val.table_rows hc)
    rw [hrows] at hextract
    exact ⟨out, Descriptor.buildRoots_ofTable p a b domain hd t ht hp out hextract⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- The actual producer succeeds exactly on the original valid domains. -/
theorem Descriptor.buildRoots_isSome (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) :
    (∃ out, Descriptor.buildRoots sign context p a b = .ok (some out)) ↔
      HexSturmMathlib.Domain f hz p a b := by
  constructor
  · rintro ⟨out, hout⟩
    exact Descriptor.buildRoots_domain f hz h1 ha hs hm hnat hsign hn hi hout
  · exact Descriptor.buildRoots_success f hz h1 ha hs hm hnat hsign hn hi context p a b

include h1 ha hs hm hnat hsign in
/-- Every successful actual root list is strictly sorted by the mathematical
order of its selected roots. The proof interprets the existing finite sorting
result, rather than sorting a separately constructed list. -/
theorem Descriptor.buildRoots_ordered {context : Ctx} {p : DensePoly E}
    {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : Descriptor.buildRoots sign context p a b = .ok (some out)) :
    (out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  apply (Descriptor.buildRoots_sorted h).imp
  intro left right hc
  obtain ⟨guard, _⟩ := Descriptor.fullOrder_eq hc
  have ho := left.fullOrder_root f hz h1 ha hs hm hnat hsign right
    guard.1 guard.2.1 guard.2.2
  have he := Option.some.inj (hc.symm.trans ho)
  by_contra hnot
  by_cases hreverse : right.root f hz h1 ha hs hm hnat hsign <
      left.root f hz h1 ha hs hm hnat hsign <;> simp [hnot, hreverse] at he

include hz h1 ha hs hm hnat hn hi hsign in
/-- On every valid domain, the actual producer returns every mathematical
root exactly once and in strictly increasing order. The domain may use finite
or infinite endpoints; coefficient storage need not be injective. -/
theorem Descriptor.buildRoots_roots (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (hdom : HexSturmMathlib.Domain f hz p a b) :
    ∃ out, Descriptor.buildRoots sign context p a b = .ok (some out) ∧
      (∀ x, x ∈ Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f) ↔
        x ∈ out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)) ∧
      (out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)).Nodup ∧
      (out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)).Pairwise (· < ·) := by
  obtain ⟨out, hout⟩ := Descriptor.buildRoots_success f hz h1 ha hs hm hnat hsign
    hn hi context p a b hdom
  obtain ⟨hcover, hnd⟩ := Descriptor.buildRoots_coverage f hz h1 ha hs hm hnat hsign hout
  exact ⟨out, hout, hcover, hnd, Descriptor.buildRoots_ordered f hz h1 ha hs hm hnat hsign hout⟩

end Hex.SignDet
