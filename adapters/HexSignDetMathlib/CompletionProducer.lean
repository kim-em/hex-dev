/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.SelectedProducer

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

omit [One E] [Add E] [Sub E] [DecidableEq Ctx]
    [IsStrictOrderedRing K] [IsRealClosed K] in
include hm hnat in
/-- The canonical full query list consists of the actual iterated derivatives. -/
theorem RawDescriptor.full_at (raw : RawDescriptor E Ctx) (x : K) :
    signsAt f hz (raw.full []).queries x =
      (List.range raw.head.natDegree).map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j + 1]
          (interpret f hz raw.head)).eval x) : Int)) := by
  simp only [signsAt, RawDescriptor.queries, RawDescriptor.full, List.map_map]
  apply List.map_congr_left
  intro j hj
  have hlt : j < raw.head.natDegree := List.mem_range.mp hj
  have hindex : j < (derivativesFrom raw.head raw.head.natDegree).length := by
    rw [derivativesFrom_length]
    exact hlt
  simp only [Function.comp_apply, Nat.add_sub_cancel, derivatives]
  rw [List.getElem?_eq_getElem hindex, Option.getD_some]
  rw [derivativesFrom_get f hz hnat hm raw.head raw.head.natDegree j hlt]

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include hm hnat in
/-- Restricting the full word at any point gives the descriptor's indexed
query word at that same point, including empty partial encodings. -/
theorem Descriptor.select_full_at {context : Ctx}
    (d : Descriptor E Ctx sign context) (x : K) :
    Thom.select d.raw.indices (signsAt f hz (d.raw.full []).queries x) =
      some (signsAt f hz d.raw.queries x) := by
  have hw := (RawDescriptor.check_eq d.accepted).1
  have hb : ∀ j ∈ d.raw.indices, 1 ≤ j ∧ j ≤ d.raw.head.natDegree :=
    fun j hj => d.raw.wellFormed_bounds hw j hj
  rw [d.raw.full_at f hz hm hnat x, d.derivatives_at f hz hm hnat x]
  exact Thom.select_full d.raw.head.natDegree
    (fun j => (SignType.sign ((Polynomial.derivative^[j]
      (interpret f hz d.raw.head)).eval x) : Int)) d.raw.indices hb

include h1 ha hs hm hnat hsign in
/-- The complete derivative table has exactly one count-one word restricting
to a validated partial encoding. Root uniqueness comes from the source's
complete count-one table, rather than an assumed Thom ordering theorem. -/
theorem Descriptor.completion_rows {context : Ctx}
    (d : Descriptor E Ctx sign context) (t : Replay E Ctx)
    (hc : t.check sign context d.raw.head d.raw.lower d.raw.upper
      (d.raw.full []).queries = true) :
    t.node.system.tableRows.toList.filter
      (fun row => decide (Thom.select d.raw.indices row.1 = some d.raw.signs)) =
        [(signsAt f hz (d.raw.full []).queries
          (d.root f hz h1 ha hs hm hnat hsign), 1)] := by
  let x := d.root f hz h1 ha hs hm hnat hsign
  let word := signsAt f hz (d.raw.full []).queries x
  let table := t.table hc
  let candidates := table.rows.toList.filter
    (fun row => decide (Thom.select d.raw.indices row.1 = some d.raw.signs))
  obtain ⟨hx, hsx⟩ := d.root_spec f hz h1 ha hs hm hnat hsign
  have hselect : Thom.select d.raw.indices word = some d.raw.signs := by
    rw [d.select_full_at f hz hm hnat x]
    exact congrArg some hsx
  have unique (y : K)
      (hy : y ∈ Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f))
      (v : List Int) (hv : signsAt f hz (d.raw.full []).queries y = v)
      (hp : Thom.select d.raw.indices v = some d.raw.signs) : y = x := by
    apply d.root_unique f hz h1 ha hs hm hnat hsign y hy
    have h := d.select_full_at f hz hm hnat y
    rw [hv, hp] at h
    exact Option.some.inj h.symm
  have hfiber : ((Tarski.rootsIn (interpret f hz d.raw.head)
      (d.raw.lower.map f) (d.raw.upper.map f)).filter
        (fun y => signsAt f hz (d.raw.full []).queries y = word)) = {x} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact unique y (Finset.mem_filter.mp hy).1 word (Finset.mem_filter.mp hy).2 hselect
  have count (v : List Int) : table.count v =
      ((Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f)).filter
          (fun y => signsAt f hz (d.raw.full []).queries y = v)).card := by
    rw [t.table_lookup hc]
    exact t.count_roots f hz h1 ha hs hm hnat sign hsign context
      d.raw.head d.raw.lower d.raw.upper (d.raw.full []).queries hc v
  have hone : table.count word = 1 := by rw [count, hfiber, Finset.card_singleton]
  obtain ⟨n, hn⟩ := table.mem_of_count_pos (by omega : 0 < table.count word)
  have hn1 : n = 1 := (table.count_mem hn).symm.trans hone
  subst n
  have member : (word, 1) ∈ candidates :=
    List.mem_filter.mpr ⟨hn, by simpa only [decide_eq_true_eq] using hselect⟩
  have only : ∀ row ∈ candidates, row = (word, 1) := by
    intro row hr
    obtain ⟨hmrow, hp⟩ := List.mem_filter.mp hr
    have hpositive := (table.wellFormed row hmrow).2.2
    have hrowcount := table.count_mem hmrow
    have hcard : 0 < ((Tarski.rootsIn (interpret f hz d.raw.head)
        (d.raw.lower.map f) (d.raw.upper.map f)).filter
          (fun y => signsAt f hz (d.raw.full []).queries y = row.1)).card := by
      rw [← count, hrowcount]
      exact hpositive
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
    obtain ⟨hyd, hyv⟩ := Finset.mem_filter.mp hy
    have hyx := unique y hyd row.1 hyv (of_decide_eq_true hp)
    have hfirst : row.1 = word := by simpa only [hyx] using hyv.symm
    have hsecond : row.2 = 1 := by rw [← hrowcount, hfirst, hone]
    exact Prod.ext hfirst hsecond
  have nd : candidates.Nodup := (List.Nodup.of_map Prod.fst table.distinct).filter _
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
/-- The actual completion algorithm succeeds for every validated descriptor
under lawful coefficients. Preparation and the complete BKR table are
constructed here; no successful result or count-one full word is assumed. -/
theorem Descriptor.buildCompletion_success {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    ∃ c : Completion d, d.buildCompletion = .ok c := by
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
      context domain bindings.1 (d.raw.full []).queries true
    have hcheck : t.val.check sign context d.raw.head d.raw.lower d.raw.upper
        (d.raw.full []).queries = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    apply d.buildCompletion_ofTable domain hd t ht
      (signsAt f hz (d.raw.full []).queries (d.root f hz h1 ha hs hm hnat hsign))
    exact d.completion_rows f hz h1 ha hs hm hnat hsign t.val hcheck

include hz h1 ha hs hm hnat hn hi hsign in
/-- Successful completion preserves the original root and returns its full
formal-derivative word. This also covers empty partial encodings. -/
theorem Descriptor.buildCompletion_roots {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    ∃ c : Completion d, d.buildCompletion = .ok c ∧
      c.descriptor.root f hz h1 ha hs hm hnat hsign =
        d.root f hz h1 ha hs hm hnat hsign ∧
      c.descriptor.raw.signs = (List.range d.raw.head.natDegree).map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j + 1]
          (interpret f hz d.raw.head)).eval
          (d.root f hz h1 ha hs hm hnat hsign)) : Int)) := by
  obtain ⟨c, h⟩ := d.buildCompletion_success f hz h1 ha hs hm hnat hsign hn hi
  exact ⟨c, h, c.root_eq_source f hz h1 ha hs hm hnat hsign,
    c.signs_at_source f hz h1 ha hs hm hnat hsign⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- The total completion operation uses the actual successful producer,
excluding its unchanged-source error fallback under lawful coefficients. -/
theorem Descriptor.complete_success {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    ∃ c : Completion d, d.buildCompletion = .ok c ∧ d.complete = c.descriptor := by
  obtain ⟨c, h⟩ := d.buildCompletion_success f hz h1 ha hs hm hnat hsign hn hi
  exact ⟨c, h, d.complete_ofBuild c h⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- Total completion preserves the selected root and literal source bindings
and returns every formal derivative sign in canonical slot order. -/
theorem Descriptor.complete_correct {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    d.complete.root f hz h1 ha hs hm hnat hsign =
        d.root f hz h1 ha hs hm hnat hsign ∧
      d.raw.completes d.complete.raw = true ∧
      d.complete.raw.indices = (List.range d.raw.head.natDegree).map (· + 1) ∧
      d.complete.raw.signs = (List.range d.raw.head.natDegree).map (fun j =>
        (SignType.sign ((Polynomial.derivative^[j + 1]
          (interpret f hz d.raw.head)).eval
          (d.root f hz h1 ha hs hm hnat hsign)) : Int)) := by
  obtain ⟨c, _, he⟩ := d.complete_success f hz h1 ha hs hm hnat hsign hn hi
  rw [he]
  exact ⟨c.root_eq_source f hz h1 ha hs hm hnat hsign, c.agrees,
    c.bindings.2.2.2.2.1, c.signs_at_source f hz h1 ha hs hm hnat hsign⟩

end Hex.SignDet
