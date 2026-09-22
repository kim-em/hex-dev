/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.Complete

public section

namespace Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [NatCast E] [DecidableEq Ctx]

/-- Insert a realized full encoding by the largest-differing-index rule.
An impossible rule or duplicate word is an internal error, never a guessed
order. Every comparison checks the common head and full derivative slots. -/
def Thom.insert {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) :
    List (Descriptor E Ctx sign context) → Except BuildError (List (Descriptor E Ctx sign context))
  | [] => .ok [d]
  | e :: es =>
    match d.fullOrder e with
    | some .lt => .ok (d :: e :: es)
    | some .gt => match insert d es with
      | .ok rest => .ok (e :: rest)
      | .error err => .error err
    | _ => .error .system

/-- Successful ordering preserves every descriptor and introduces none. -/
theorem Thom.insert_perm {sign : E → Int} {context : Ctx}
    (d : Descriptor E Ctx sign context) {ds out : List (Descriptor E Ctx sign context)}
    (h : insert d ds = .ok out) : out.Perm (d :: ds) := by
  induction ds generalizing out with
  | nil => simpa [insert] using h.symm
  | cons e es ih =>
    cases hc : d.fullOrder e with
    | none => simp [insert, hc] at h
    | some order =>
      cases order with
      | eq => simp [insert, hc] at h
      | lt =>
        have he : out = d :: e :: es := by simpa [insert, hc] using h.symm
        rw [he]
      | gt =>
        cases hi : insert d es with
        | error err => simp [insert, hc, hi] at h
        | ok rest =>
          have he : out = e :: rest := by simpa [insert, hc, hi] using h.symm
          rw [he]
          exact (List.Perm.cons e (ih hi)).trans (List.Perm.swap _ _ _)

/-- Finite insertion preserves strict sortedness under the stated comparator
laws. The companion must obtain those laws for realized encodings from Thom
order; this theorem does not assume or assert that foundation. -/
theorem Thom.insert_sorted {sign : E → Int} {context : Ctx}
    (htrans : ∀ a b c : Descriptor E Ctx sign context,
      a.fullOrder b = some .lt → b.fullOrder c = some .lt → a.fullOrder c = some .lt)
    (hreverse : ∀ a b : Descriptor E Ctx sign context,
      a.fullOrder b = some .gt → b.fullOrder a = some .lt)
    (d : Descriptor E Ctx sign context) {ds out : List (Descriptor E Ctx sign context)}
    (hs : ds.Pairwise (fun a b => a.fullOrder b = some .lt))
    (h : insert d ds = .ok out) : out.Pairwise (fun a b => a.fullOrder b = some .lt) := by
  induction ds generalizing out with
  | nil =>
    have he : out = [d] := by simpa [insert] using h.symm
    simp [he]
  | cons e es ih =>
    obtain ⟨he, hes⟩ := List.pairwise_cons.mp hs
    cases hc : d.fullOrder e with
    | none => simp [insert, hc] at h
    | some order =>
      cases order with
      | eq => simp [insert, hc] at h
      | lt =>
        have hout : out = d :: e :: es := by simpa [insert, hc] using h.symm
        rw [hout]
        apply List.pairwise_cons.mpr
        refine ⟨?_, List.pairwise_cons.mpr ⟨he, hes⟩⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hc
        · exact htrans d e x hc (he x hx)
      | gt =>
        cases hi : insert d es with
        | error err => simp [insert, hc, hi] at h
        | ok rest =>
          have hout : out = e :: rest := by simpa [insert, hc, hi] using h.symm
          rw [hout]
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hes hi⟩
          intro x hx
          have hm := (insert_perm d hi).mem_iff.mp hx
          rcases List.mem_cons.mp hm with rfl | hm
          · exact hreverse x e hc
          · exact he x hm

/-- Extract a full count-one row from a shared checked table. Table invariants
prove the sign shape and lookup; no derivative computation or replay is repeated. -/
def Descriptor.ofFullRow {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    (row : List Int × Nat) (hm : row ∈ (t.table hc).rows.toList) (hone : row.2 = 1) :
    Descriptor E Ctx sign context :=
  ofTable (raw.full row.1) t
    (raw.full_wellFormed row.1 hp
      (((t.table hc).wellFormed row hm).1.trans (raw.full_queries_length []))
      (List.all_eq_true.mpr (fun s hs => decide_eq_true (((t.table hc).wellFormed row hm).2.1 s hs))))
    hctx hc (((t.table hc).count_mem hm).trans hone)

theorem Descriptor.ofFullRow_raw {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    (row : List Int × Nat) (hm : row ∈ (t.table hc).rows.toList) (hone : row.2 = 1) :
    (ofFullRow raw t hp hctx hc row hm hone).raw = raw.full row.1 := by
  unfold ofFullRow
  exact ofTable_raw _ _ _ _ _ _

theorem Descriptor.ofReplay_ofFullRow {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    (row : List Int × Nat) (hm : row ∈ (t.table hc).rows.toList) (hone : row.2 = 1) :
    ofReplay? sign context (raw.full row.1) t = some (ofFullRow raw t hp hctx hc row hm hone) := by
  unfold ofFullRow
  exact ofReplay_ofTable _ _ _ _ _ _

/-- Enumerate rows from one checked full table. Only the count-one guard and
Thom insertion run per row; domain/query replay and derivative extraction are shared. -/
def Descriptor.rootsFromTable {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true) :
    (rows : List (List Int × Nat)) →
    (∀ row ∈ rows, row ∈ (t.table hc).rows.toList) →
    Except BuildError (List (Descriptor E Ctx sign context))
  | [], _ => .ok []
  | row :: rows, hrows =>
    if hone : row.2 = 1 then do
      let rest ← rootsFromTable raw t hp hctx hc rows
        (fun row hr => hrows row (List.mem_cons_of_mem _ hr))
      Thom.insert (ofFullRow raw t hp hctx hc row (hrows row (by simp)) hone) rest
    else .error .system

/-- Convert a full table to count-one descriptors in Thom order. This helper
checks each raw descriptor against the same complete replay, so an invented
word or a count greater than one cannot become a root descriptor. -/
def Descriptor.rootsFrom (sign : E → Int) (context : Ctx) (raw : RawDescriptor E Ctx)
    (t : Replay E Ctx) : List (List Int × Nat) →
      Except BuildError (List (Descriptor E Ctx sign context))
  | [] => .ok []
  | (signs, count) :: rows =>
    if count ≠ 1 then .error .system
    else match Descriptor.ofReplay? sign context (raw.full signs) t with
      | none => .error .replay
      | some d => match rootsFrom sign context raw t rows with
        | .error err => .error err
        | .ok ds => Thom.insert d ds

/-- Shared extraction is exactly the literal per-descriptor checking path,
including its ordering and diagnostics, on rows of the accepted full table. -/
theorem Descriptor.rootsFromTable_eq {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    (rows : List (List Int × Nat)) (hrows : ∀ row ∈ rows, row ∈ (t.table hc).rows.toList) :
    rootsFromTable raw t hp hctx hc rows hrows = rootsFrom sign context raw t rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨signs, count⟩ := row
    by_cases hone : count = 1
    · subst count
      simp only [rootsFromTable, rootsFrom, ne_eq, not_true_eq_false,
        ↓reduceDIte, ↓reduceIte]
      rw [ofReplay_ofFullRow raw t hp hctx hc (signs, 1) (hrows _ (by simp)) rfl]
      simp only [ih, bind, Except.bind]
      cases rootsFrom sign context raw t rows <;> rfl
    · simp only [rootsFromTable, rootsFrom, hone, ne_eq, not_false_eq_true,
        ↓reduceDIte, ↓reduceIte]

/-- Successful root-list construction keeps exactly the table's encoding
words. It cannot drop a difficult row or add a guessed root while sorting. -/
theorem Descriptor.rootsFrom_perm (sign : E → Int) (context : Ctx)
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx) {rows : List (List Int × Nat)}
    {out : List (Descriptor E Ctx sign context)}
    (h : rootsFrom sign context raw t rows = .ok out) :
    (out.map fun d => d.raw.signs).Perm (rows.map Prod.fst) := by
  induction rows generalizing out with
  | nil =>
    have he : out = [] := by simpa [rootsFrom] using h.symm
    simp [he]
  | cons row rows ih =>
    obtain ⟨signs, count⟩ := row
    by_cases hn : count ≠ 1
    · simp [rootsFrom, hn] at h
    · cases hd : ofReplay? sign context (raw.full signs) t with
      | none => simp [rootsFrom, hn, hd] at h
      | some d =>
        cases hr : rootsFrom sign context raw t rows with
        | error err => simp [rootsFrom, hn, hd, hr] at h
        | ok ds =>
          have hi : Thom.insert d ds = .ok out := by simpa [rootsFrom, hn, hd, hr] using h
          have hs : d.raw.signs = signs := by rw [ofReplay_raw hd]; rfl
          have hp := (Thom.insert_perm d hi).map (fun d => d.raw.signs)
          simp only [List.map_cons, hs] at hp
          exact hp.trans (List.Perm.cons signs (ih hr))

/-- Successful enumeration is strictly sorted under the finite comparator
laws. Their correspondence with real-root order is a separate companion gate. -/
theorem Descriptor.rootsFrom_sorted (sign : E → Int) (context : Ctx)
    (htrans : ∀ a b c : Descriptor E Ctx sign context,
      a.fullOrder b = some .lt → b.fullOrder c = some .lt → a.fullOrder c = some .lt)
    (hreverse : ∀ a b : Descriptor E Ctx sign context,
      a.fullOrder b = some .gt → b.fullOrder a = some .lt)
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx) {rows : List (List Int × Nat)}
    {out : List (Descriptor E Ctx sign context)}
    (h : rootsFrom sign context raw t rows = .ok out) :
    out.Pairwise (fun a b => a.fullOrder b = some .lt) := by
  induction rows generalizing out with
  | nil =>
    have he : out = [] := by simpa [rootsFrom] using h.symm
    simp [he]
  | cons row rows ih =>
    obtain ⟨signs, count⟩ := row
    by_cases hn : count ≠ 1
    · simp [rootsFrom, hn] at h
    · cases hd : ofReplay? sign context (raw.full signs) t with
      | none => simp [rootsFrom, hn, hd] at h
      | some d =>
        cases hr : rootsFrom sign context raw t rows with
        | error err => simp [rootsFrom, hn, hd, hr] at h
        | ok ds =>
          have hi : Thom.insert d ds = .ok out := by simpa [rootsFrom, hn, hd, hr] using h
          exact Thom.insert_sorted htrans hreverse d (ih hr) hi

/-- Shared extraction preserves every input row, by its exact correspondence
with the literal per-descriptor checking path. -/
theorem Descriptor.rootsFromTable_perm {sign : E → Int} {context : Ctx}
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    {rows : List (List Int × Nat)} (hrows : ∀ row ∈ rows, row ∈ (t.table hc).rows.toList)
    {out : List (Descriptor E Ctx sign context)}
    (h : rootsFromTable raw t hp hctx hc rows hrows = .ok out) :
    (out.map fun d => d.raw.signs).Perm (rows.map Prod.fst) :=
  rootsFrom_perm sign context raw t ((rootsFromTable_eq raw t hp hctx hc rows hrows).symm.trans h)

/-- Shared extraction retains the finite strict sortedness guarantee. -/
theorem Descriptor.rootsFromTable_sorted {sign : E → Int} {context : Ctx}
    (htrans : ∀ a b c : Descriptor E Ctx sign context,
      a.fullOrder b = some .lt → b.fullOrder c = some .lt → a.fullOrder c = some .lt)
    (hreverse : ∀ a b : Descriptor E Ctx sign context,
      a.fullOrder b = some .gt → b.fullOrder a = some .lt)
    (raw : RawDescriptor E Ctx) (t : Replay E Ctx)
    (hp : 0 < raw.head.natDegree) (hctx : raw.context = context)
    (hc : t.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true)
    {rows : List (List Int × Nat)} (hrows : ∀ row ∈ rows, row ∈ (t.table hc).rows.toList)
    {out : List (Descriptor E Ctx sign context)}
    (h : rootsFromTable raw t hp hctx hc rows hrows = .ok out) :
    out.Pairwise (fun a b => a.fullOrder b = some .lt) :=
  rootsFrom_sorted sign context htrans hreverse raw t
    ((rootsFromTable_eq raw t hp hctx hc rows hrows).symm.trans h)

variable [Neg E] [Inv E]

/-- Enumerate all full encodings and order them by Thom's rule. Only invalid
root domains return `none`; unproved producer/Thom invariants stay separate
internal diagnostics. Constants admit no well-formed full encoding; their
branch retains the literal per-descriptor checking path. -/
def Descriptor.buildRoots (sign : E → Int) (context : Ctx) (p : DensePoly E)
    (a b : Endpoint E) : Except BuildError (Option (List (Descriptor E Ctx sign context))) :=
  match hd : Sturm.prepare sign p a b with
  | none => .ok none
  | some domain =>
    let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
    match buildPrepared context domain (raw.full []).queries with
    | .error err => .error err
    | .ok t =>
      have bindings := Sturm.prepare_eq_some sign p a b domain hd
      have hc : t.val.check sign context raw.head raw.lower raw.upper (raw.full []).queries = true := by
        simpa only [bindings.1, bindings.2.1, bindings.2.2.1, bindings.2.2.2] using t.property
      let table := t.val.table hc
      let result := if hp : 0 < p.natDegree then
        rootsFromTable raw t.val hp rfl hc table.rows.toList (fun _ hm => hm)
        else rootsFrom sign context raw t.val table.rows.toList
      match result with
      | .error err => .error err
      | .ok roots => .ok (some roots)

/-- Successful public root construction extracts from its actual prepared
BKR table. Both degree branches agree with literal per-descriptor replay. -/
theorem Descriptor.buildRoots_spec {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : buildRoots sign context p a b = .ok (some out)) :
    let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
    ∃ domain, Sturm.prepare sign p a b = some domain ∧
      ∃ t, buildPrepared context domain (raw.full []).queries = .ok t ∧
        rootsFrom sign context raw t.val t.val.node.system.tableRows.toList = .ok out := by
  dsimp only
  unfold buildRoots at h
  split at h
  · cases h
  · rename_i domain hd
    dsimp only at h
    split at h
    · contradiction
    · rename_i t ht
      refine ⟨domain, hd, t, ht, ?_⟩
      simp only [rootsFromTable_eq, dite_eq_ite, ite_self, Replay.table_rows] at h
      split at h
      · contradiction
      · cases h
        assumption

/-- The public entry point preserves all full sign words of the actual
produced table, including when the constant branch returns an empty list. -/
theorem Descriptor.buildRoots_perm {sign : E → Int} {context : Ctx} {p : DensePoly E}
    {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : buildRoots sign context p a b = .ok (some out)) :
    let raw : RawDescriptor E Ctx := ⟨context, p, a, b, [], []⟩
    ∃ domain, Sturm.prepare sign p a b = some domain ∧
      ∃ t, buildPrepared context domain (raw.full []).queries = .ok t ∧
        (out.map fun d => d.raw.signs).Perm (t.val.node.system.tableRows.toList.map Prod.fst) := by
  obtain ⟨domain, hd, t, ht, hs⟩ := buildRoots_spec h
  exact ⟨domain, hd, t, ht, rootsFrom_perm sign context _ _ hs⟩

/-- The public entry point is strictly sorted under the same explicit finite
comparator laws as insertion. Thom semantics must still supply those laws. -/
theorem Descriptor.buildRoots_sorted {sign : E → Int} {context : Ctx}
    (htrans : ∀ a b c : Descriptor E Ctx sign context,
      a.fullOrder b = some .lt → b.fullOrder c = some .lt → a.fullOrder c = some .lt)
    (hreverse : ∀ a b : Descriptor E Ctx sign context,
      a.fullOrder b = some .gt → b.fullOrder a = some .lt)
    {p : DensePoly E} {a b : Endpoint E} {out : List (Descriptor E Ctx sign context)}
    (h : buildRoots sign context p a b = .ok (some out)) :
    out.Pairwise (fun a b => a.fullOrder b = some .lt) := by
  obtain ⟨_, _, t, _, hs⟩ := buildRoots_spec h
  exact rootsFrom_sorted sign context htrans hreverse _ t.val hs

end Hex.SignDet
