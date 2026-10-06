/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.SelectedRoot
public import HexSignDetTheory.RootProducer
public import HexSignDet.RootList

public section

namespace Hex.SignDet

open HexPolyTheory.Interpret HexRealRootsTheory

variable {E : Type u} {K : Type v} {Ctx : Type w} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [Neg E] [Inv E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K] [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (h1 : f 1 = 1) (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hnat : ∀ n : Nat, f (n : E) = (n : K))
variable {sign : E → Int} (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

variable (hn : ∀ a, f (-a) = -f a) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)

include hz h1 ha hs hm hnat hn hi hsign in
/-- On a valid root-free domain the actual producer succeeds with an empty
list. This discharges both extraction branches without a Thom foundation;
both table production success and its counts use the shared proved
root-sum theorem. -/
theorem Descriptor.buildRoots_empty (context : Ctx) (p : DensePoly E) (a b : Endpoint E)
    (hdom : HexSturmTheory.Domain f hz p a b)
    (hempty : Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f) = ∅) :
    Descriptor.buildRoots sign context p a b = .ok (some []) := by
  let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
  have hsg := HexSturmTheory.sign_spec f sign hsign
  have hp : (Sturm.prepare sign p a b).isSome = true :=
    (HexSturmTheory.prepare_isSome f hz ha hs hm sign
      (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
      h1 hn hi hnat (fun a => (hsg a).1) p a b).mpr hdom
  cases hd : Sturm.prepare sign p a b with
  | none => simp only [hd, Option.isSome_none, Bool.false_eq_true] at hp
  | some domain =>
    have bindings := Sturm.prepare_eq_some sign p a b domain hd
    obtain ⟨t, ht, _⟩ := buildPrepared_roots f hz h1 ha hs hm hnat hn hi sign hsign
      context domain bindings.1 (raw.full []).queries true
    have hc : t.val.check sign context p a b (raw.full []).queries = true := by
      simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
    have hr : t.val.node.system.tableRows.toList = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro row hrow
      have member : row ∈ (t.val.table hc).rows.toList := by
        simpa only [Replay.table_rows] using hrow
      have positive := ((t.val.table hc).wellFormed row member).2.2
      have count := (t.val.table hc).count_mem member
      rw [Replay.table_lookup] at count
      rw [t.val.count_roots f hz h1 ha hs hm hnat sign hsign
        context p a b (raw.full []).queries hc row.1, hempty,
        Finset.filter_empty, Finset.card_empty] at count
      omega
    exact Descriptor.buildRoots_ofEmpty p a b domain hd t ht hr

include hz h1 ha hs hm hnat hn hi hsign in
/-- Actual enumeration succeeds on every valid domain containing at most
one root. Count-one extraction and insertion into the empty list need no
Thom injectivity or ordering foundation, including for non-Archimedean fields.
Table production success and counts use the shared proved root-sum theorem. -/
theorem Descriptor.buildRoots_subsingleton (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (hdom : HexSturmTheory.Domain f hz p a b)
    (hsmall : (Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)).card ≤ 1) :
    ∃ out, Descriptor.buildRoots sign context p a b = .ok (some out) := by
  let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
  let roots := Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f)
  change roots.card ≤ 1 at hsmall
  have hsg := HexSturmTheory.sign_spec f sign hsign
  have hprepared : (Sturm.prepare sign p a b).isSome = true :=
    (HexSturmTheory.prepare_isSome f hz ha hs hm sign
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
    have member (row : List Int × Nat) (hr : row ∈ t.val.node.system.tableRows.toList) :
        row ∈ table.rows.toList := by
      simpa only [table, Replay.table_rows] using hr
    have meaning (row : List Int × Nat) (hr : row ∈ t.val.node.system.tableRows.toList) :
        row.2 = (roots.filter fun x => signsAt f hz (raw.full []).queries x = row.1).card := by
      have count := table.count_mem (member row hr)
      rw [Replay.table_lookup, t.val.count_roots f hz h1 ha hs hm hnat sign hsign
        context p a b (raw.full []).queries hc row.1] at count
      exact count.symm
    have witness (row : List Int × Nat) (hr : row ∈ t.val.node.system.tableRows.toList) :
        ∃ x ∈ roots, signsAt f hz (raw.full []).queries x = row.1 := by
      have positive := (table.wellFormed row (member row hr)).2.2
      rw [meaning row hr] at positive
      obtain ⟨x, hx⟩ := Finset.card_pos.mp positive
      exact ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    cases hr : t.val.node.system.tableRows.toList with
    | nil => exact ⟨[], Descriptor.buildRoots_ofEmpty p a b domain hd t ht hr⟩
    | cons row rest =>
      have hrow : row ∈ t.val.node.system.tableRows.toList := by rw [hr]; simp
      obtain ⟨x, hx, hword⟩ := witness row hrow
      have positive := (table.wellFormed row (member row hrow)).2.2
      have countBound := Finset.card_filter_le roots
        (fun x => signsAt f hz (raw.full []).queries x = row.1)
      rw [← meaning row hrow] at countBound
      have hone : row.2 = 1 := by omega
      have hrest : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other hother
        obtain ⟨y, hy, hyword⟩ := witness other (by rw [hr]; exact List.mem_cons_of_mem _ hother)
        have hxy : x = y := Finset.card_le_one.mp hsmall x hx y hy
        have he : other.1 = row.1 := hyword.symm.trans (hxy ▸ hword)
        have distinct := table.distinct
        simp only [table, Replay.table_rows, hr, List.map_cons, List.nodup_cons] at distinct
        exact distinct.1 (List.mem_map.mpr ⟨other, hother, he⟩)
      have hp : 0 < p.natDegree := by
        have rootPositive : 0 < roots.card := Finset.card_pos.mpr ⟨x, hx⟩
        have bound := Tarski.rootsIn_card_le (interpret f hz p) (a.map f) (b.map f)
        rw [natDegree_interpret] at bound
        change roots.card ≤ p.natDegree at bound
        omega
      exact Descriptor.buildRoots_ofSingle p a b domain hd t ht row
        (by simpa only [hrest] using hr) hone hp

include hz h1 ha hs hm hnat hn hi hsign in
/-- Nonzero constant heads on a valid domain return an actual empty list.
Success is proved rather than assumed, with no Thom foundation. -/
theorem Descriptor.buildRoots_constant_success (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (hdom : HexSturmTheory.Domain f hz p a b)
    (hp : p.natDegree = 0) :
    Descriptor.buildRoots sign context p a b = .ok (some []) := by
  apply Descriptor.buildRoots_empty f hz h1 ha hs hm hnat hsign hn hi context p a b hdom
  apply Finset.card_eq_zero.mp
  have bound := Tarski.rootsIn_card_le (interpret f hz p) (a.map f) (b.map f)
  rw [natDegree_interpret, hp] at bound
  omega

include hz h1 ha hs hm hnat hn hi hsign in
/-- Actual enumeration succeeds for linear heads on every valid domain.
The degree bound supplies the small-root-set premise, without a separating
interval or Thom foundation. Success uses the shared proved root-sum theorem. -/
theorem Descriptor.buildRoots_linear (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) (hdom : HexSturmTheory.Domain f hz p a b)
    (hp : p.natDegree = 1) :
    ∃ out, Descriptor.buildRoots sign context p a b = .ok (some out) := by
  apply Descriptor.buildRoots_subsingleton f hz h1 ha hs hm hnat hsign hn hi
    context p a b hdom
  have bound := Tarski.rootsIn_card_le (interpret f hz p) (a.map f) (b.map f)
  simpa only [natDegree_interpret, hp] using bound

omit [IsRealClosed K] in
include hz h1 ha hs hm hnat hn hi hsign in
/-- Successful enumeration retains the caller's valid mathematical domain.
This follows from accepted replay and does not use the root-sum theorem. -/
theorem Descriptor.buildRoots_domain {context : Ctx} {p : DensePoly E}
    {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : Descriptor.buildRoots sign context p a b = .ok (some out)) :
    HexSturmTheory.Domain f hz p a b := by
  obtain ⟨domain, hd, _, _, _⟩ := Descriptor.buildRoots_spec h
  have hsg := HexSturmTheory.sign_spec f sign hsign
  exact (HexSturmTheory.prepare_sound f hz ha hs hm sign
    (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
    h1 hn hi hnat (fun a => (hsg a).1) p a b domain hd).1

omit [IsRealClosed K] in
include hz h1 ha hs hm hnat hn hi hsign in
/-- The absent-domain result characterizes exactly invalid mathematical
domains, without the root-sum theorem or a producer-success premise. -/
theorem Descriptor.buildRoots_none_iff (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) :
    Descriptor.buildRoots sign context p a b = .ok none ↔
      ¬ HexSturmTheory.Domain f hz p a b := by
  rw [Descriptor.buildRoots_none]
  have hsg := HexSturmTheory.sign_spec f sign hsign
  have validity := HexSturmTheory.prepare_isSome f hz ha hs hm sign
    (fun a => (hsg a).2.1) (fun a => (hsg a).2.2.1)
    h1 hn hi hnat (fun a => (hsg a).1) p a b
  rw [← validity]
  cases Sturm.prepare sign p a b <;> simp

include h1 ha hs hm hnat hsign in
/-- Every successful actual root enumeration covers all roots exactly once.
This interprets accepted output without assuming a root-separating interval
or Thom order. `ThomRoots` separately proves success on all valid domains
and strict mathematical sorting. -/
theorem Descriptor.buildRoots_coverage {context : Ctx} {p : DensePoly E}
    {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : Descriptor.buildRoots sign context p a b = .ok (some out)) :
    (∀ x, x ∈ Tarski.rootsIn (interpret f hz p) (a.map f) (b.map f) ↔
      x ∈ out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)) ∧
      (out.map (fun d => d.root f hz h1 ha hs hm hnat hsign)).Nodup := by
  let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
  obtain ⟨domain, hd, t, _, hp⟩ := Descriptor.buildRoots_perm h
  have bindings := Sturm.prepare_eq_some sign p a b domain hd
  have hc : t.val.check sign context p a b (raw.full []).queries = true := by
    simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
  let table := t.val.table hc
  have literal (d : Descriptor E Ctx sign context) (hd : d ∈ out) :
      d.raw.head = p ∧ d.raw.lower = a ∧ d.raw.upper = b ∧
        d.raw.queries = (raw.full []).queries := by
    obtain ⟨word, he⟩ := Descriptor.buildRoots_raw h d hd
    rw [he]
    exact ⟨rfl, rfl, rfl, raw.full_queries word⟩
  have rootWord (d : Descriptor E Ctx sign context) (hd : d ∈ out) :
      signsAt f hz (raw.full []).queries (d.root f hz h1 ha hs hm hnat hsign) =
        d.raw.signs := by
    rw [← (literal d hd).2.2.2]
    exact (d.root_spec f hz h1 ha hs hm hnat hsign).2
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hx
      let word := signsAt f hz (raw.full []).queries x
      have hpositive : 0 < table.count word := by
        rw [Replay.table_lookup]
        rw [t.val.count_roots f hz h1 ha hs hm hnat sign hsign
          context p a b (raw.full []).queries hc word]
        exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
      obtain ⟨n, hn⟩ := table.mem_of_count_pos hpositive
      have hword : word ∈ t.val.node.system.tableRows.toList.map Prod.fst := by
        apply List.mem_map.mpr
        refine ⟨(word, n), ?_, rfl⟩
        simpa only [table, Replay.table_rows] using hn
      obtain ⟨d, hd, he⟩ := List.mem_map.mp (hp.mem_iff.mpr hword)
      have hdroot : x = d.root f hz h1 ha hs hm hnat hsign := by
        apply d.root_unique f hz h1 ha hs hm hnat hsign x
        · simpa only [(literal d hd).1, (literal d hd).2.1,
            (literal d hd).2.2.1] using hx
        · rw [(literal d hd).2.2.2, he]
      exact List.mem_map.mpr ⟨d, hd, hdroot.symm⟩
    · intro hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      simpa only [(literal d hd).1, (literal d hd).2.1,
        (literal d hd).2.2.1] using (d.root_spec f hz h1 ha hs hm hnat hsign).1
  · have hwords : (out.map fun d => d.raw.signs).Nodup :=
      hp.nodup_iff.mpr (by simpa only [table, Replay.table_rows] using table.distinct)
    have hpair : out.Pairwise (fun d e => d.raw.signs ≠ e.raw.signs) :=
      List.pairwise_map.mp hwords
    apply List.pairwise_map.mpr
    apply hpair.imp_of_mem
    intro d e hd he hne heq
    apply hne
    exact (rootWord d hd).symm.trans (by rw [heq]; exact rootWord e he)

end Hex.SignDet
