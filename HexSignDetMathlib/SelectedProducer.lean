/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootProducer
public import HexSignDetMathlib.SelectedRoot

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret HexRealRootsMathlib

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

include h1 ha hs hm hnat hsign in
/-- In any accepted complete joint table, exactly one count-one row extends
the descriptor's signs. Its suffix is the query word at the selected root.
This uses root uniqueness and complete counts, without a Thom order theorem. -/
theorem Descriptor.signs_rows {context : Ctx} (d : Descriptor E Ctx sign context)
    (qs : List (DensePoly E)) (t : Replay E Ctx)
    (hc : t.check sign context d.raw.head d.raw.lower d.raw.upper
      (d.raw.queries ++ qs) = true) :
    t.node.system.tableRows.toList.filter
      (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs)) =
        [(d.raw.signs ++ signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign), 1)] := by
  let x := d.root f hz h1 ha hs hm hnat hsign
  let word := d.raw.signs ++ signsAt f hz qs x
  let table := t.table hc
  let candidates := table.rows.toList.filter
    (fun row => decide (row.1.take d.raw.queries.length = d.raw.signs))
  obtain ⟨hx, hsx⟩ := d.root_spec f hz h1 ha hs hm hnat hsign
  have hlen : d.raw.signs.length = d.raw.queries.length := by
    simpa only [signsAt, List.length_map] using congrArg List.length hsx.symm
  have hword : signsAt f hz (d.raw.queries ++ qs) x = word := by
    change signsAt f hz (d.raw.queries ++ qs) x = d.raw.signs ++ signsAt f hz qs x
    rw [show signsAt f hz (d.raw.queries ++ qs) x =
      signsAt f hz d.raw.queries x ++ signsAt f hz qs x by simp only [signsAt, List.map_append]]
    rw [show signsAt f hz d.raw.queries x = d.raw.signs from hsx]
  have hprefix : word.take d.raw.queries.length = d.raw.signs := by
    simp only [word, ← hlen, List.take_left]
  have unique (y : K)
      (hy : y ∈ Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f))
      (v : List Int) (hv : signsAt f hz (d.raw.queries ++ qs) y = v)
      (hp : v.take d.raw.queries.length = d.raw.signs) : y = x := by
    apply d.root_unique f hz h1 ha hs hm hnat hsign y hy
    have h := congrArg (List.take d.raw.queries.length) hv
    simpa [signsAt, List.take_append, hp] using h
  have hfiber : ((Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
        (fun y => signsAt f hz (d.raw.queries ++ qs) y = word)) = {x} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hx, hword⟩, ?_⟩
    intro y hy
    exact unique y (Finset.mem_filter.mp hy).1 word (Finset.mem_filter.mp hy).2 hprefix
  have count (v : List Int) : table.count v =
      ((Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f)).filter
          (fun y => signsAt f hz (d.raw.queries ++ qs) y = v)).card := by
    rw [t.table_lookup hc]
    exact t.count_roots f hz h1 ha hs hm hnat sign hsign context
      d.raw.head d.raw.lower d.raw.upper (d.raw.queries ++ qs) hc v
  have hone : table.count word = 1 := by rw [count, hfiber, Finset.card_singleton]
  obtain ⟨n, hn⟩ := table.mem_of_count_pos (by omega : 0 < table.count word)
  have hn1 : n = 1 := (table.count_mem hn).symm.trans hone
  subst n
  have member : (word, 1) ∈ candidates :=
    List.mem_filter.mpr ⟨hn, by simpa only [decide_eq_true_eq] using hprefix⟩
  have only : ∀ row ∈ candidates, row = (word, 1) := by
    intro row hr
    obtain ⟨hmrow, hp⟩ := List.mem_filter.mp hr
    have hpositive := (table.wellFormed row hmrow).2.2
    have hrowcount := table.count_mem hmrow
    have hcard : 0 < ((Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f)).filter
          (fun y => signsAt f hz (d.raw.queries ++ qs) y = row.1)).card := by
      rw [← count, hrowcount]
      exact hpositive
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
    obtain ⟨hyd, hyv⟩ := Finset.mem_filter.mp hy
    have hyx := unique y hyd row.1 hyv (of_decide_eq_true hp)
    have hfirst : row.1 = word := by simpa only [hyx, hword] using hyv.symm
    have hsecond : row.2 = 1 := by rw [← hrowcount, hfirst, hone]
    exact Prod.ext hfirst hsecond
  have nd : candidates.Nodup :=
    (List.Nodup.of_map Prod.fst table.distinct).filter _
  have hsize : candidates.length ≤ 1 := by
    apply nd.length_le_of_subset (l₂ := [(word, 1)])
    intro row hr
    exact List.mem_singleton.mpr (only row hr)
  have hnonempty : candidates.length ≠ 0 := by
    intro hzero
    rw [List.length_eq_zero_iff.mp hzero] at member
    contradiction
  obtain ⟨row, hrow⟩ := List.length_eq_one_iff.mp (by omega : candidates.length = 1)
  have heq := only row (by rw [hrow]; exact List.mem_singleton_self _)
  have result := hrow.trans (congrArg (fun r => [r]) heq)
  simpa only [candidates, table, t.table_rows hc, word, x] using result

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- The actual selected-sign constructor always succeeds on a validated
descriptor with lawful coefficients. No successful table or selected-sign
certificate is assumed; preparation, BKR construction and all final guards
are discharged from the descriptor's accepted unique-root evidence. -/
theorem Descriptor.buildSigns_success {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E)) :
    ∃ s : SelectedSigns d qs, d.buildSigns qs = .ok s := by
  obtain ⟨_, _, hc, _⟩ := RawDescriptor.check_eq d.accepted
  have hdomain := d.evidence.check_domain f hz h1 ha hs hm hnat sign hsign
    context d.raw.head d.raw.lower d.raw.upper d.raw.queries hc
  have hsg := HexSturmMathlib.sign_spec f sign hsign
  have hp : (Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper).isSome = true :=
    (HexSturmMathlib.prepare_isSome f hz ha hs hm sign
      (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
      h1 hn hi hnat (fun a => (hsg a).1) d.raw.head d.raw.lower d.raw.upper).mpr hdomain
  cases hd : Sturm.prepare sign d.raw.head d.raw.lower d.raw.upper with
  | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hp
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign d.raw.head d.raw.lower d.raw.upper domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 (d.raw.queries ++ qs) true
    have hcheck : t.val.check sign context d.raw.head d.raw.lower d.raw.upper
        (d.raw.queries ++ qs) = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    let values : Vector Int qs.length :=
      ⟨(signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign)).toArray, by simp [signsAt]⟩
    apply d.buildSigns_ofTable qs domain hd t ht values
    simpa only [values, Vector.toList_mk, List.toList_toArray] using
      d.signs_rows f hz h1 ha hs hm hnat hsign qs t.val hcheck

include hz h1 ha hs hm hnat hn hi hsign in
/-- Successful construction returns precisely the ordered signs at the
descriptor's original root, including empty lists and repeated queries. -/
theorem Descriptor.buildSigns_roots {context : Ctx}
    (d : Descriptor E Ctx sign context) (qs : List (DensePoly E)) :
    ∃ s : SelectedSigns d qs, d.buildSigns qs = .ok s ∧
      s.values.toList = signsAt f hz qs (d.root f hz h1 ha hs hm hnat hsign) := by
  obtain ⟨s, hbuild⟩ := d.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi qs
  exact ⟨s, hbuild, s.values_at_root f hz h1 ha hs hm hnat hsign⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- The single-query total operation uses an actual successful checked
construction. In particular its internal error fallback is unreachable. -/
theorem Descriptor.signAt_success {context : Ctx}
    (d : Descriptor E Ctx sign context) (q : DensePoly E) :
    ∃ s : SelectedSigns d [q], d.buildSigns [q] = .ok s ∧ d.signAt q = s.value := by
  obtain ⟨s, h⟩ := d.buildSigns_success f hz h1 ha hs hm hnat hsign hn hi [q]
  exact ⟨s, h, d.signAt_ofBuild q s h⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- The total single-query operation is the mathematical evaluation sign at
the original selected root. It requires no injective stored representation. -/
theorem Descriptor.signAt_correct {context : Ctx}
    (d : Descriptor E Ctx sign context) (q : DensePoly E) :
    d.signAt q = (SignType.sign ((interpret f hz q).eval
      (d.root f hz h1 ha hs hm hnat hsign)) : Int) := by
  obtain ⟨s, _, h⟩ := d.signAt_success f hz h1 ha hs hm hnat hsign hn hi q
  rw [h]
  exact s.value_at_root f hz h1 ha hs hm hnat hsign

end Hex.SignDet
