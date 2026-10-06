/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.ReencodingProducer
public import HexSignDetTheory.CompletionProducer

public section

namespace Hex.SignDet

open HexPolyTheory.Interpret HexRealRootsTheory

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
/-- Whenever the target contains the source root, an accepted complete joint
table has exactly one matching row, with count one. This does not yet prove
that the target derivative word alone is a valid descriptor. -/
theorem Descriptor.reencoding_rows {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f))
    (t : Replay E Ctx)
    (hc : t.check sign context head a b
      (((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries ++
        source.raw.constraints) = true) :
    t.node.system.tableRows.toList.filter
      (fun row => decide (row.1.drop
        ((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries.length =
          source.raw.constraintSigns)) =
      [(signsAt f hz ((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries
        (source.root f hz h1 ha hs hm hnat hsign) ++ source.raw.constraintSigns, 1)] := by
  let raw : RawDescriptor E Ctx := ⟨context, head, a, b, [], []⟩
  let fullQueries := (raw.full []).queries
  let qs := fullQueries ++ source.raw.constraints
  let x := source.root f hz h1 ha hs hm hnat hsign
  let word := signsAt f hz fullQueries x ++ source.raw.constraintSigns
  let table := t.table hc
  let candidates := table.rows.toList.filter
    (fun row => decide (row.1.drop fullQueries.length = source.raw.constraintSigns))
  have hword : signsAt f hz qs x = word := by
    simp only [qs, word, signsAt, List.map_append]
    exact congrArg (fun tail => signsAt f hz fullQueries x ++ tail)
      (source.constraints_at_root f hz h1 ha hs hm hnat hsign)
  have htail : word.drop fullQueries.length = source.raw.constraintSigns := by
    simp only [word, signsAt, ← List.length_map
      (f := fun q => (SignType.sign ((interpret f hz q).eval x) : Int)), List.drop_left]
  have unique (y : K) (hv : signsAt f hz qs y = word) : y = x := by
    apply (source.constraints_iff f hz h1 ha hs hm hnat hsign y).mp
    have h := congrArg (List.drop fullQueries.length) hv
    simpa [qs, signsAt, htail] using h
  have hfiber : ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
      (fun y => signsAt f hz qs y = word)) = {x} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hmem, hword⟩, ?_⟩
    intro y hy
    exact unique y (Finset.mem_filter.mp hy).2
  have count (v : List Int) : table.count v =
      ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
        (fun y => signsAt f hz qs y = v)).card := by
    rw [t.table_lookup hc]
    exact t.count_roots f hz h1 ha hs hm hnat sign hsign context head a b qs hc v
  have hone : table.count word = 1 := by rw [count, hfiber, Finset.card_singleton]
  obtain ⟨n, hn⟩ := table.mem_of_count_pos (by omega : 0 < table.count word)
  have hn1 : n = 1 := (table.count_mem hn).symm.trans hone
  subst n
  have member : (word, 1) ∈ candidates :=
    List.mem_filter.mpr ⟨hn, by simpa only [decide_eq_true_eq] using htail⟩
  have only : ∀ row ∈ candidates, row = (word, 1) := by
    intro row hr
    obtain ⟨hmrow, hp⟩ := List.mem_filter.mp hr
    have positive := (table.wellFormed row hmrow).2.2
    have hrowcount := table.count_mem hmrow
    have cardpos : 0 < ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
        (fun y => signsAt f hz qs y = row.1)).card := by
      rw [← count, hrowcount]
      exact positive
    obtain ⟨y, hy⟩ := Finset.card_pos.mp cardpos
    have hyv := (Finset.mem_filter.mp hy).2
    have h := congrArg (List.drop fullQueries.length) hyv
    have constraints : signsAt f hz source.raw.constraints y = source.raw.constraintSigns := by
      simpa [qs, signsAt, of_decide_eq_true hp] using h
    have hyx := (source.constraints_iff f hz h1 ha hs hm hnat hsign y).mp constraints
    have hfirst : row.1 = word := by rw [hyx, hword] at hyv; exact hyv.symm
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
  simpa only [candidates, table, t.table_rows hc, fullQueries, word, raw, x] using result

include h1 ha hs hm hnat hsign in
/-- A mathematically equal target polynomial has the same full derivative
word. On a contained root domain, the validated source partial word supplies
uniqueness without a general Thom injectivity theorem. -/
theorem Descriptor.reencoding_fiber {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (hhead : interpret f hz head = interpret f hz source.raw.head)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f))
    (hsubset : Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f) ⊆
      Tarski.rootsIn (interpret f hz source.raw.head)
        (source.raw.lower.map f) (source.raw.upper.map f)) :
    ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
      (fun y => signsAt f hz
        ((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries y =
        signsAt f hz ((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries
          (source.root f hz h1 ha hs hm hnat hsign))) =
      {source.root f hz h1 ha hs hm hnat hsign} := by
  let x := source.root f hz h1 ha hs hm hnat hsign
  have hqs (z : K) :
      signsAt f hz ((⟨context, head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries z =
        signsAt f hz (source.raw.full []).queries z :=
    RawDescriptor.full_congr f hz hm hnat _ source.raw hhead z
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hmem, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨hyd, hv⟩ := Finset.mem_filter.mp hy
  rw [hqs y, hqs x] at hv
  apply source.root_unique f hz h1 ha hs hm hnat hsign y (hsubset hyd)
  have hselected := source.select_full_at f hz hm hnat y
  rw [hv, source.select_full_at f hz hm hnat x] at hselected
  exact (Option.some.inj hselected).symm.trans
    (source.root_spec f hz h1 ha hs hm hnat hsign).2

include h1 ha hs hm hnat hsign in
/-- On a smaller root domain of the same defining polynomial, the full word
at the retained source root identifies that root uniquely. The old validated
partial word supplies uniqueness; no general Thom injectivity is used. -/
theorem Descriptor.refinement_fiber {context : Ctx}
    (source : Descriptor E Ctx sign context) (a b : Endpoint E)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz source.raw.head) (a.map f) (b.map f))
    (hsubset : Tarski.rootsIn (interpret f hz source.raw.head) (a.map f) (b.map f) ⊆
      Tarski.rootsIn (interpret f hz source.raw.head)
        (source.raw.lower.map f) (source.raw.upper.map f)) :
    ((Tarski.rootsIn (interpret f hz source.raw.head) (a.map f) (b.map f)).filter
      (fun y => signsAt f hz
        ((⟨context, source.raw.head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries y =
        signsAt f hz ((⟨context, source.raw.head, a, b, [], []⟩ : RawDescriptor E Ctx).full []).queries
          (source.root f hz h1 ha hs hm hnat hsign))) =
      {source.root f hz h1 ha hs hm hnat hsign} := by
  exact source.reencoding_fiber f hz h1 ha hs hm hnat hsign source.raw.head a b
    rfl hmem hsubset

variable [Neg E] [Inv E]
variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- Re-encoding succeeds for a differently stored, mathematically equal
defining polynomial on a valid contained root domain retaining the source
root. The actual producer builds fresh evidence; no literal polynomial
equality, injective coefficient representation or Thom foundation is assumed. -/
theorem Descriptor.buildReencoding_congr {context : Ctx}
    (source : Descriptor E Ctx sign context) (head : DensePoly E) (a b : Endpoint E)
    (hhead : (head - source.raw.head).isZero = true)
    (hdom : HexSturmTheory.Domain f hz head a b)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f))
    (hsubset : Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f) ⊆
      Tarski.rootsIn (interpret f hz source.raw.head)
        (source.raw.lower.map f) (source.raw.upper.map f)) :
    ∃ r : Reencoding source head a b,
      source.buildReencoding head a b = .ok (some r) ∧
      r.target.root f hz h1 ha hs hm hnat hsign =
        source.root f hz h1 ha hs hm hnat hsign := by
  have hpoly : interpret f hz head = interpret f hz source.raw.head :=
    (sub_isZero f hz hs head source.raw.head).mp hhead
  let raw : RawDescriptor E Ctx := ⟨context, head, a, b, [], []⟩
  let fullQueries := (raw.full []).queries
  let x := source.root f hz h1 ha hs hm hnat hsign
  let fullWord := signsAt f hz fullQueries x
  let word := fullWord ++ source.raw.constraintSigns
  let targetRaw := raw.full fullWord
  have hsg := HexSturmTheory.sign_spec f sign hsign
  have hprepared : (Sturm.prepare sign head a b).isSome = true :=
    (HexSturmTheory.prepare_isSome f hz ha hs hm sign
      (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
      h1 hn hi hnat (fun a => (hsg a).1) head a b).mpr hdom
  cases hd : Sturm.prepare sign head a b with
  | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hprepared
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign head a b domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 (fullQueries ++ source.raw.constraints) true
    have hc : t.val.check sign context head a b
        (fullQueries ++ source.raw.constraints) = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    have hrows : (t.val.node.system.tableRows.toList.filter fun row =>
        decide (row.1.drop fullQueries.length = source.raw.constraintSigns)) = [(word, 1)] :=
      source.reencoding_rows f hz h1 ha hs hm hnat hsign head a b hmem t.val hc
    have hp : 0 < raw.head.natDegree := by
      have hw := (RawDescriptor.check_eq source.accepted).1
      simp only [RawDescriptor.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hdegree : head.natDegree = source.raw.head.natDegree := by
        rw [← natDegree_interpret f hz head, hpoly, natDegree_interpret]
      exact hdegree.symm ▸ hw.1.1.1.1
    have hlen : fullWord.length = raw.head.natDegree := by
      simpa only [fullWord, signsAt, List.length_map, fullQueries] using raw.full_queries_length []
    have hsigns : fullWord.all (fun s => decide (s = -1 ∨ s = 0 ∨ s = 1)) = true := by
      apply List.all_eq_true.mpr
      intro s hs
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hs
      generalize SignType.sign ((interpret f hz q).eval x) = z
      cases z <;> simp
    have hw : targetRaw.wellFormed = true := raw.full_wellFormed fullWord hp hlen hsigns
    have hfiber := source.reencoding_fiber f hz h1 ha hs hm hnat hsign head a b hpoly hmem hsubset
    have hone : ((Tarski.rootsIn (interpret f hz targetRaw.head)
        (targetRaw.lower.map f) (targetRaw.upper.map f)).filter
          (fun y => signsAt f hz targetRaw.queries y = targetRaw.signs)).card = 1 := by
      change ((Tarski.rootsIn (interpret f hz head) (a.map f) (b.map f)).filter
        (fun y => signsAt f hz fullQueries y = fullWord)).card = 1
      rw [hfiber, Finset.card_singleton]
    obtain ⟨target, hbuild⟩ := Descriptor.build_of_unique_root f hz h1 ha hs hm hnat hn hi
      sign hsign context targetRaw rfl hw domain hd hone
    have hraw := Descriptor.build_raw hbuild
    have hmember : (word, 1) ∈ t.val.node.system.tableRows.toList := by
      have h : (word, 1) ∈ (t.val.node.system.tableRows.toList.filter fun row =>
          decide (row.1.drop fullQueries.length = source.raw.constraintSigns)) := by
        rw [hrows]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp h).1
    have htableMember : (word, 1) ∈ (t.val.table hc).rows.toList := by
      simpa only [Replay.table_rows] using hmember
    have hcount : t.val.node.system.count word = 1 :=
      (t.val.table_lookup hc word).symm.trans ((t.val.table hc).count_mem htableMember)
    have hcheck : source.checkReencoding target head a b t.val = true := by
      simp only [Descriptor.checkReencoding, hraw, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨rfl, rfl, rfl⟩, hc⟩, hcount⟩
    have htake : word.take fullQueries.length = fullWord := by
      have hl : fullWord.length = fullQueries.length := by simp only [fullWord, signsAt, List.length_map]
      simp only [word, ← hl, List.take_left]
    obtain ⟨r, hr⟩ := source.buildReencoding_ofTable head a b domain hd t ht
      word hrows target (by
        change Descriptor.build sign context (raw.full (word.take fullQueries.length)) = _
        rw [htake]
        exact hbuild) hcheck
    exact ⟨r, hr, r.root_eq_source f hz h1 ha hs hm hnat hsign⟩

include hz h1 ha hs hm hnat hn hi hsign in
/-- Re-encoding succeeds on a valid smaller interval of the same defining
polynomial when that interval retains the selected root. The original partial
descriptor supplies uniqueness, including on non-Archimedean fields. -/
theorem Descriptor.buildReencoding_refinement {context : Ctx}
    (source : Descriptor E Ctx sign context) (a b : Endpoint E)
    (hdom : HexSturmTheory.Domain f hz source.raw.head a b)
    (hmem : source.root f hz h1 ha hs hm hnat hsign ∈
      Tarski.rootsIn (interpret f hz source.raw.head) (a.map f) (b.map f))
    (hsubset : Tarski.rootsIn (interpret f hz source.raw.head) (a.map f) (b.map f) ⊆
      Tarski.rootsIn (interpret f hz source.raw.head)
        (source.raw.lower.map f) (source.raw.upper.map f)) :
    ∃ r : Reencoding source source.raw.head a b,
      source.buildReencoding source.raw.head a b = .ok (some r) ∧
      r.target.root f hz h1 ha hs hm hnat hsign =
        source.root f hz h1 ha hs hm hnat hsign := by
  exact source.buildReencoding_congr f hz h1 ha hs hm hnat hsign hn hi
    source.raw.head a b ((sub_isZero f hz hs _ _).mpr rfl) hdom hmem hsubset

end Hex.SignDet
