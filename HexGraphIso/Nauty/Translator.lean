/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CertAutom
public import HexGraphIso.Nauty.Search
public import HexGraphIso.Nauty.CanonForm

public section

/-!
Layers one and two of the verified search refinement
(SPEC § Verified search refinement): properties of the trace-driven
certificate translator.

Layer one is total production: `produceCand G none` always returns a
candidate, because an absent budget cannot exhaust — `charge` is the
identity, and no other producer step touches the budget fields.

Layer two's foundation is automorphism closure: `checkAutom` is
closed under the producer's witness composition, so every witness
composed from individually-valid generators is itself valid.

The programme is complete: `certifyCanon?_isSome` is proved in
`SearchOutcomeCertify.lean`. It did not take the route this file's
statements anticipated, and the section following the closure toolkit
records where each layer-two obligation actually landed.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-! # Layer one: total production under an absent budget -/

theorem charge_of_budget_none {st : AutState}
    (h : st.budget = none) : st.charge = st := by
  rw [AutState.charge, h]

theorem admit_budget (ctx : Ctx n) (st : AutState) (γ : Array Nat) :
    (st.admit ctx γ).budget = st.budget := by
  rw [AutState.admit]
  simp only [Id.run, pure]
  repeat' split
  all_goals rfl

theorem admit_exhausted (ctx : Ctx n) (st : AutState) (γ : Array Nat) :
    (st.admit ctx γ).exhausted = st.exhausted := by
  rw [AutState.admit]
  simp only [Id.run, pure]
  repeat' split
  all_goals rfl

theorem harvest_budget (ctx : Ctx n) (st : AutState) (lab : Array Nat) :
    (st.harvest ctx lab).budget = st.budget := by
  rw [AutState.harvest]
  simp only [Id.run, pure]
  repeat' split
  all_goals simp only [admit_budget]

theorem harvest_exhausted (ctx : Ctx n) (st : AutState)
    (lab : Array Nat) :
    (st.harvest ctx lab).exhausted = st.exhausted := by
  rw [AutState.harvest]
  simp only [Id.run, pure]
  repeat' split
  all_goals simp only [admit_exhausted]

/-- A fold preserves any invariant its step preserves. -/
theorem foldl_preserves {α σ : Type} (P : σ → Prop) (g : σ → α → σ)
    (h : ∀ s a, P s → P (g s a)) :
    ∀ (l : List α) (s : σ), P s → P (l.foldl g s)
  | [], _, hs => hs
  | a :: t, s, hs => foldl_preserves P g h t (g s a) (h s a hs)

theorem certifyNodeAutom_budget (ctx : Ctx n) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active : VSet n) (numcells : Nat) (bcodes : List Nat) (st : AutState),
      st.budget = none →
      (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
        bcodes st).2.budget = none ∧
      (certifyNodeAutom ctx tcLevel fuel level lab ptn active numcells
        bcodes st).2.exhausted = st.exhausted
  | 0, _, _, _, _, _, _, st, hb => ⟨hb, rfl⟩
  | fuel + 1, level, lab, ptn, active, numcells, bcodes, st, hb => by
    rw [certifyNodeAutom.eq_def]
    simp only [charge_of_budget_none hb]
    repeat' split
    all_goals try exact ⟨hb, rfl⟩
    all_goals try exact ⟨(harvest_budget ..).trans hb,
      harvest_exhausted ..⟩
    all_goals
      refine foldl_preserves
        (fun acc : List CertNode × AutState ×
            Option (Nat × Array (Array Nat × Array Nat)) =>
          acc.2.1.budget = none ∧
            acc.2.1.exhausted = st.exhausted)
        _ (fun s a hs => ?_) _ (([], st, none)) ⟨hb, rfl⟩
      try dsimp only
      repeat' split
      all_goals
        first
        | exact hs
        | exact ⟨(certifyNodeAutom_budget ctx tcLevel fuel
              _ _ _ _ _ _ _ hs.1).1,
            (certifyNodeAutom_budget ctx tcLevel fuel
              _ _ _ _ _ _ _ hs.1).2.trans hs.2⟩

/-- Layer one: the trace-driven producer is total under an absent
budget — nothing in the walk can exhaust it. -/
theorem produceCand_none_isSome {k : Nat} (G : Colored n k) :
    (produceCand G none).isSome := by
  have hfold := foldl_preserves
    (fun st : AutState => st.budget = none ∧ st.exhausted = false)
    (fun st γ => st.admit { g := rowsOf G } γ)
    (fun st γ hst => ⟨(admit_budget ..).trans hst.1,
      (admit_exhausted ..).trans hst.2⟩)
    (runColoredTraced G).autos.toList
    (AutState.init n none) ⟨rfl, rfl⟩
  rw [Array.foldl_toList] at hfold
  have hcert := certifyNodeAutom_budget { g := rowsOf G } 100
    n 1 (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2)
    (initActive n (initialPartition G).2)
    (initialPartition G).2.length
    ((runColoredTraced G).bestCodes ++ [codeSentinel])
    { (runColoredTraced G).autos.foldl
        (fun st γ => st.admit { g := rowsOf G } γ)
        (AutState.init n none) with
      refLeaf := some (runColoredTraced G).result.canonlab }
    hfold.1
  simp only [produceCand, Option.any]
  rw [ite_eq_right (by simp)]
  rw [hcert.2]
  have hex : ({ (runColoredTraced G).autos.foldl
      (fun st γ => st.admit { g := rowsOf G } γ)
      (AutState.init n none) with
    refLeaf := some (runColoredTraced G).result.canonlab } :
      AutState).exhausted = false := hfold.2
  rw [hex]
  rfl

/-! # Graph facts for `rowsOf`: dischargers for the row-set hypotheses

`checkAutom_of_isautom` below is stated graph-agnostically over a row
array with symmetry, looplessness, and per-row bounds; these lemmas
discharge those hypotheses for `rowsOf G`. -/

theorem rowsOf_symm {k : Nat} (G : Colored n k) :
    ∀ i j, i < n → j < n →
      ((rowsOf G)[i]!).mem j = ((rowsOf G)[j]!).mem i := by
  intro i j hi hj
  rw [getElem!_rowsOf G hi, getElem!_rowsOf G hj,
    mem_rowOf_lt G hi hj, mem_rowOf_lt G hj hi,
    G.graph.adj_symm ⟨i, hi⟩ ⟨j, hj⟩]

theorem rowsOf_loopless {k : Nat} (G : Colored n k) :
    ∀ i, i < n → ((rowsOf G)[i]!).mem i = false := by
  intro i hi
  rw [getElem!_rowsOf G hi, mem_rowOf_lt G hi hi,
    G.graph.adj_self ⟨i, hi⟩]

/-! # Layer two, foundation: `checkAutom` closure under composition -/

theorem composePerm_getElem! (f π : Array Nat) {nn v : Nat}
    (hv : v < nn) : (composePerm f π nn)[v]! = f[π[v]!]! := by
  rw [composePerm, getElem!_pos _ _ (by simpa using hv),
    Array.getElem_map, Array.getElem_range]

theorem composePerm_size (f π : Array Nat) (nn : Nat) :
    (composePerm f π nn).size = nn := by
  rw [composePerm, Array.size_map, Array.size_range]

/-- `image` composes when the inner map stays in range. -/
theorem image_comp (σ τ : Nat → Nat) (s : VSet n)
    (hτ : ∀ v, v < n → τ v < n) :
    s.image (fun w => σ (τ w)) = (s.image τ).image σ := by
  refine VSet.ext fun w => ?_
  rw [VSet.mem_image, VSet.mem_image, Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hc⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    refine ⟨τ v, List.mem_range.mpr (hτ v (List.mem_range.mp hv)), ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨?_, hc.1.2⟩, hc.2⟩
    rw [VSet.mem_image, List.any_eq_true]
    refine ⟨v, hv, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hc.1.1, rfl⟩, hτ v (List.mem_range.mp hv)⟩
  · rintro ⟨u, hu, hc⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨hmem, hσ⟩, hlt⟩ := hc
    rw [VSet.mem_image, List.any_eq_true] at hmem
    obtain ⟨v, hv, hvc⟩ := hmem
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hvc
    refine ⟨v, hv, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hvc.1.1, by rw [hvc.1.2]; exact hσ⟩, by rw [hvc.1.2]; exact hlt⟩

/-- `checkAutom` is closed under the producer's witness
composition. -/
theorem checkAutom_compose {g : Array (VSet n)} {f π : Array Nat}
    (hf : checkAutom g f = true) (hπ : checkAutom g π = true) :
    checkAutom g (composePerm f π n) = true := by
  rw [checkAutom] at hf hπ ⊢
  simp only [Bool.and_eq_true] at hf hπ
  obtain ⟨⟨⟨hfs, hfb⟩, hfp⟩, hfr⟩ := hf
  obtain ⟨⟨⟨hπs, hπb⟩, hπp⟩, hπr⟩ := hπ
  have hπb' : ∀ v, v < n → π[v]! < n := fun v hv => by
    simpa using List.all_eq_true.mp hπb v (List.mem_range.mpr hv)
  have hfb' : ∀ v, v < n → f[v]! < n := fun v hv => by
    simpa using List.all_eq_true.mp hfb v (List.mem_range.mpr hv)
  have hχ : ∀ v, v < n → (composePerm f π n)[v]! = f[π[v]!]! :=
    fun v hv => composePerm_getElem! f π hv
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using composePerm_size f π n, ?_⟩, ?_⟩, ?_⟩
  · refine List.all_eq_true.mpr fun v hv => ?_
    have hvn := List.mem_range.mp hv
    simp only [hχ v hvn]
    simpa using hfb' _ (hπb' v hvn)
  · have hmap : ((List.range n).map fun v =>
        (composePerm f π n)[v]!) =
        (((List.range n).map fun v => π[v]!).map fun u => f[u]!) := by
      rw [List.map_map]
      exact List.map_congr_left fun v hv =>
        hχ v (List.mem_range.mp hv)
    rw [List.isPerm_iff] at hfp hπp ⊢
    rw [hmap]
    exact ((hπp.map fun u => f[u]!).trans hfp)
  · refine List.all_eq_true.mpr fun v hv => ?_
    have hvn := List.mem_range.mp hv
    have hfr' := List.all_eq_true.mp hfr (π[v]!)
      (List.mem_range.mpr (hπb' v hvn))
    have hπr' := List.all_eq_true.mp hπr v hv
    simp only [beq_iff_eq] at hfr' hπr' ⊢
    rw [hχ v hvn, hfr', hπr',
      ← image_comp (fun w => f[w]!) (fun w => π[w]!) _ hπb']
    exact image_congr _ fun w hw => (hχ w hw).symm

/-- The identity image of a set is itself. -/
theorem image_id (s : VSet n) : s.image (fun w => w) = s := by
  refine VSet.ext fun w => ?_
  rw [VSet.mem_image, Bool.eq_iff_iff, List.any_eq_true]
  constructor
  · rintro ⟨v, _, hc⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rw [← hc.1.2]
    exact hc.1.1
  · intro hw
    refine ⟨w, List.mem_range.mpr (VSet.mem_lt hw), ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨hw, rfl⟩, VSet.mem_lt hw⟩

/-- `checkAutom` is closed under inversion, for bounded row sets. -/
theorem checkAutom_invPerm {g : Array (VSet n)} {γ : Array Nat}
    (hγ : checkAutom g γ = true) :
    checkAutom g (invPerm γ) = true := by
  rw [checkAutom] at hγ ⊢
  simp only [Bool.and_eq_true] at hγ
  obtain ⟨⟨⟨hsize, hbound⟩, hperm⟩, hrows⟩ := hγ
  have hsz : γ.size = n := by simpa using hsize
  have hbound' : ∀ v, v < n → γ[v]! < n := fun v hv => by
    simpa using List.all_eq_true.mp hbound v (List.mem_range.mpr hv)
  have hnodup : (((List.range n).map fun v => γ[v]!)).Nodup :=
    ((List.isPerm_iff.mp hperm).symm.nodup List.nodup_range)
  have hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
    intro a b ha hb' hab
    have hga : ((List.range n).map fun v => γ[v]!)[a]! = γ[a]! := by
      rw [getElem!_pos _ _ (by simpa using ha), List.getElem_map,
        List.getElem_range]
    have hgb : ((List.range n).map fun v => γ[v]!)[b]! = γ[b]! := by
      rw [getElem!_pos _ _ (by simpa using hb'), List.getElem_map,
        List.getElem_range]
    exact (List.Nodup.getElem!_inj (by simpa using ha)
      (by simpa using hb') hnodup).mp (by rw [hga, hgb]; exact hab)
  have hsurj : ∀ u, u < n → ∃ v, v < n ∧ γ[v]! = u := by
    intro u hu
    have hmem : u ∈ ((List.range n).map fun v => γ[v]!) :=
      (List.isPerm_iff.mp hperm).symm.mem_iff.mp
        (List.mem_range.mpr hu)
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hmem
    exact ⟨v, List.mem_range.mp hv, he⟩
  have hδγ : ∀ v, v < n → (invPerm γ)[γ[v]!]! = v := by
    intro v hv
    exact getElem!_invPerm γ
      (fun a b ha hb' => hinj a b (by omega) (by omega))
      (by omega) (by rw [hsz]; exact hbound' v hv)
  have hδlt : ∀ u, u < n → (invPerm γ)[u]! < n := fun u hu => by
    have := getElem!_invPerm_lt (lab := γ)
      (by omega : 0 < γ.size) u
    omega
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using (invPerm_size γ).trans hsz, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun u hu => by
      simpa using hδlt u (List.mem_range.mp hu)
  · rw [List.isPerm_iff]
    have hmapid : (((List.range n).map fun v => γ[v]!).map
        fun u => (invPerm γ)[u]!) = List.range n := by
      rw [List.map_map]
      refine (List.map_congr_left fun v hv => ?_).trans
        (List.map_id _)
      show (invPerm γ)[γ[v]!]! = v
      exact hδγ v (List.mem_range.mp hv)
    have hp := (List.isPerm_iff.mp hperm).symm.map
      fun u => (invPerm γ)[u]!
    rw [hmapid] at hp
    exact hp
  · refine List.all_eq_true.mpr fun u hu => ?_
    have hun := List.mem_range.mp hu
    obtain ⟨v, hvn, hvu⟩ := hsurj u hun
    have hδu : (invPerm γ)[u]! = v := by rw [← hvu, hδγ v hvn]
    have hrv := List.all_eq_true.mp hrows v (List.mem_range.mpr hvn)
    simp only [beq_iff_eq] at hrv ⊢
    rw [hδu, ← hvu, hrv,
      ← image_comp (fun w => (invPerm γ)[w]!) (fun w => γ[w]!) _
        hbound']
    have : g[v]!.image (fun w => (invPerm γ)[γ[w]!]!) =
        g[v]!.image (fun w => w) :=
      image_congr _ fun w hw => hδγ w hw
    rw [this, image_id]

/-- The identity array is a checked automorphism of any graph with
bounded rows: the base case of witness composition. -/
theorem checkAutom_range {g : Array (VSet n)} :
    checkAutom g (Array.range n) = true := by
  rw [checkAutom]
  have hget : ∀ v, v < n → (Array.range n)[v]! = v := fun v hv => by
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_range]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simp, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr fun v hv => by
      have hvn := List.mem_range.mp hv
      simp only [hget v hvn]
      simpa using hvn
  · rw [List.isPerm_iff]
    refine List.Perm.of_eq ?_
    refine (List.map_congr_left fun v hv => ?_).trans (List.map_id _)
    show (Array.range n)[v]! = v
    exact hget v (List.mem_range.mp hv)
  · refine List.all_eq_true.mpr fun v hv => ?_
    have hvn := List.mem_range.mp hv
    simp only [beq_iff_eq]
    have : g[v]!.image (fun w => (Array.range n)[w]!) =
        g[v]!.image (fun w => w) :=
      image_congr _ fun w hw => hget w hw
    rw [hget v hvn, this, image_id _]

    rw [hget v hvn, this, image_id_of_lt (hb v hvn)]

/-!
# Where the layer-two obligations landed

`certifyCanon?_isSome` is proved (`SearchOutcomeCertify.lean`), by a
route that uses some of what this file states and replaces the rest.

* `checkAutom_of_isautom`, the counting bridge below, is live. It
  consumes `isautom_iff`, the `rowsOf` dischargers above and the
  `PopCount` comparison toolkit, and it is applied in
  `StoreValid.lean`, where `scatter_isPerm` supplies its permutation
  hypothesis: both admission sites in `processnode` push a scatter of
  one discrete leaf labelling over another, which is a permutation by
  construction. The general obligation an earlier reading of layer
  two posed here, over every `γ` in `(runColoredTraced G).autos` and
  every `composeOnto` the certify walk harvests, turned out not to be
  needed by anything.
* The validated-store invariant (`GensOk.admit`, `GensOk.init`,
  `GensOk.foldl_admit`) and witness validity (`witness?_checkAutom`)
  state store validity as an invariant of the search-side generator
  store. The landed proof does not use them: `CertStore.lean` proves
  `certifyNodeAutom_automsOk` structurally over the emitted
  certificate, because the producer checks each witness immediately
  before emitting an automorphism prune, so
  `certifyCanon?_isSome_of_keyEq` carries no store hypothesis.
* The replay spine is `certifyNode_replays` and
  `certifyCanon?_isSome_of_dominated` (`CertReplay.lean`), and its
  domination hypothesis is discharged by `canonSpecKey_eq_tracedKey`,
  which is layer three. Domination is not removable: `certifyNodeAutom`
  emits `.codePrune` on the `.gt` comparison, which the replay
  rejects, and a `.leaf` whose key exceeds the claimed suffix fails
  `keyCmp`, so an unconditional spine would have been unsound.

The closure toolkit above is the part of this file with consumers
outside it: `checkAutom_compose` and `checkAutom_range` are used by
`AutosLedger.lean` and `SearchOrbit.lean`.

## The guarded-scan `forIn` technique

`isautom` is a nested `forIn` over `[0, n)` with an early
`return false`, a loop shape with no other reasoning precedent in the
tree. The reusable technique is a "guarded scan" whose state is
`Option Bool × Unit`: it yields `(none, ())` while every element
passes and is done with `(some false, ())` on the first failure, so
the result flag is `none` exactly when every element passes
(`forIn_scan_fst_cases`, `forIn_scan_fst_eq_none`), with
`forIn_range_eq` and `id_run_scan` reducing the `[0, n)` range and the
outer `Id` do-block. `isautom_iff` below is what it buys, and the
counting bridge consumes that.

### Guarded-scan technique

The scan state: `none` means "no failure yet", `some false` means
"a failure was seen". The `Unit` mirrors `isautom`'s desugaring.-/

/-- A guarded-scan body over state `Option Bool × Unit`: on the live
state `(none, ())` it either yields `(none, ())` (the element passed)
or is done with `(some false, ())` (the element failed). -/
private def IsGate
    (body : Option Bool × Unit → Id (ForInStep (Option Bool × Unit)))
    (pass : Prop) [Decidable pass] : Prop :=
  (pass → body (none, ()) = pure (ForInStep.yield (none, ()))) ∧
  (¬ pass → body (none, ()) = pure (ForInStep.done (some false, ())))

/-- A guarded scan's result flag is `none` or `some false`, never
`some true`. -/
private theorem forIn_scan_fst_cases {α : Type} (L : List α)
    (b : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit)))
    (p : α → Prop) [DecidablePred p]
    (hgate : ∀ a, IsGate (b a) (p a)) :
    (forIn L (none, ()) b : Id (Option Bool × Unit)).1 = none ∨
      (forIn L (none, ()) b : Id (Option Bool × Unit)).1 = some false := by
  induction L with
  | nil => exact Or.inl rfl
  | cons a as ih =>
    rw [List.forIn_cons]
    by_cases h : p a
    · rw [(hgate a).1 h]
      exact ih
    · rw [(hgate a).2 h]
      exact Or.inr rfl

/-- A guarded scan's result flag is `none` exactly when every element
passes. -/
private theorem forIn_scan_fst_eq_none {α : Type} (L : List α)
    (b : α → Option Bool × Unit → Id (ForInStep (Option Bool × Unit)))
    (p : α → Prop) [DecidablePred p]
    (hgate : ∀ a, IsGate (b a) (p a)) :
    (forIn L (none, ()) b : Id (Option Bool × Unit)).1 = none ↔
      ∀ a ∈ L, p a := by
  induction L with
  | nil => exact iff_of_true rfl (by simp)
  | cons a as ih =>
    rw [List.forIn_cons]
    by_cases h : p a
    · rw [(hgate a).1 h]
      simp only [List.mem_cons, forall_eq_or_imp, h, true_and]
      exact ih
    · rw [(hgate a).2 h]
      simp only [List.mem_cons, forall_eq_or_imp]
      exact iff_of_false (by simp) (by simp [h])

/-- Membership in `s.toList`. -/
private theorem mem_toList {s : VSet n} {pos : Nat} :
    pos ∈ s.toList ↔ pos < n ∧ s.mem pos = true :=
  ⟨fun h => ⟨VSet.mem_lt (VSet.mem_toList.mp h), VSet.mem_toList.mp h⟩,
    fun h => VSet.mem_toList.mpr h.2⟩

/-- `[:n]` unfolds to a `forIn` over `List.range n`. -/
private theorem forIn_range_eq {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

/-- The outer `do` of `isautom` reduces to a match on the scan flag. -/
private theorem id_run_scan (F : Id (Option Bool × Unit)) :
    (do let __s ← F
        match __s.fst with
        | some r => pure r
        | none => pure true : Id Bool).run
      = match F.fst with | some r => r | none => true := rfl

/-! ### The `isautom` specification -/

/-- The outer loop body of `isautom`, spelled with the named core
matcher so it is syntactically identical to the `do`-desugaring
(restating it with `match` syntax would mint a fresh matcher the
unifier rejects). -/
private def isautomOuter (ctx : Ctx n) (γ : Array Nat) (i : Nat)
    (__s : Option Bool × Unit) : Id (ForInStep (Option Bool × Unit)) :=
  have row := ctx.g[i]!
  do
  let __s ← forIn row.toList (none, ()) fun pos __s =>
      if pos > i then
        if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
          pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ()))
      else pure (ForInStep.yield (none, ()))
  have __r : Option Bool × Unit := __s
  Break.runK.match_1 (fun _ => Id (ForInStep (Option Bool × Unit))) __r.fst
    (fun r => pure (ForInStep.done (some r, ()))) fun _ =>
    pure (ForInStep.yield (none, ()))

private theorem isautom_eq_scan (ctx : Ctx n) (γ : Array Nat) :
    isautom ctx γ =
      Break.runK.match_1 (fun _ => Bool)
        (forIn (List.range n) (none, ())
          (isautomOuter ctx γ) : Id (Option Bool × Unit)).fst
        (fun r => r) (fun _ => true) := by
  rw [isautom, forIn_range_eq]
  rfl

/-- The per-vertex pass condition of `isautom`'s outer loop. -/
private def isautomPass (ctx : Ctx n) (γ : Array Nat) (i : Nat) : Prop :=
  ∀ pos ∈ ctx.g[i]!.toList,
    pos > i → ctx.g[γ[i]!]!.mem γ[pos]! = true

private instance (ctx : Ctx n) (γ : Array Nat) (i : Nat) :
    Decidable (isautomPass ctx γ i) :=
  inferInstanceAs (Decidable (∀ pos ∈ _, _ → _ = true))

private theorem isautomInner_gate (ctx : Ctx n) (γ : Array Nat)
    (i pos : Nat) :
    IsGate
      (fun __s => if pos > i then
        if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
          pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ()))
      else pure (ForInStep.yield (none, ())))
      (pos > i → ctx.g[γ[i]!]!.mem γ[pos]! = true) := by
  constructor
  · intro hp
    by_cases hgt : pos > i
    · rw [ite_eq_left hgt, ite_eq_right (by simpa using hp hgt)]
    · rw [ite_eq_right hgt]
  · intro hp
    rcases Decidable.not_imp_iff_and_not.mp hp with ⟨hgt, hne⟩
    rw [ite_eq_left hgt, ite_eq_left (by simpa using hne)]

private theorem isautomOuter_gate (ctx : Ctx n) (γ : Array Nat) (i : Nat) :
    IsGate (isautomOuter ctx γ i) (isautomPass ctx γ i) := by
  have hcases := forIn_scan_fst_cases (ctx.g[i]!.toList)
    (fun pos __s => if pos > i then
        if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
          pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ()))
      else pure (ForInStep.yield (none, ())))
    (fun pos => pos > i → ctx.g[γ[i]!]!.mem γ[pos]! = true)
    (fun pos => isautomInner_gate ctx γ i pos)
  have hiff := forIn_scan_fst_eq_none (ctx.g[i]!.toList)
    (fun pos __s => if pos > i then
        if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
          pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ()))
      else pure (ForInStep.yield (none, ())))
    (fun pos => pos > i → ctx.g[γ[i]!]!.mem γ[pos]! = true)
    (fun pos => isautomInner_gate ctx γ i pos)
  constructor
  · intro hp
    show (do
      let __s ← forIn (ctx.g[i]!.toList) (none, ()) _
      have __r : Option Bool × Unit := __s
      Break.runK.match_1 (fun _ => Id (ForInStep (Option Bool × Unit)))
        __r.fst (fun r => pure (ForInStep.done (some r, ()))) fun _ =>
        pure (ForInStep.yield (none, ())) : Id _) = _
    have hnone : (forIn (ctx.g[i]!.toList) (none, ())
        (fun pos __s => if pos > i then
          if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
            pure (ForInStep.done (some false, ()))
          else pure (ForInStep.yield (none, ()))
        else pure (ForInStep.yield (none, ()))) :
        Id (Option Bool × Unit)).fst = none := hiff.mpr hp
    show Break.runK.match_1 (fun _ => Id (ForInStep (Option Bool × Unit)))
      (forIn (ctx.g[i]!.toList) (none, ()) _ :
        Id (Option Bool × Unit)).fst _ _ = _
    rw [hnone]
  · intro hp
    have hsome : (forIn (ctx.g[i]!.toList) (none, ())
        (fun pos __s => if pos > i then
          if ¬ctx.g[γ[i]!]!.mem γ[pos]! = true then
            pure (ForInStep.done (some false, ()))
          else pure (ForInStep.yield (none, ()))
        else pure (ForInStep.yield (none, ()))) :
        Id (Option Bool × Unit)).fst = some false := by
      rcases hcases with h | h
      · exact absurd (hiff.mp h) hp
      · exact h
    show Break.runK.match_1 (fun _ => Id (ForInStep (Option Bool × Unit)))
      (forIn (ctx.g[i]!.toList) (none, ()) _ :
        Id (Option Bool × Unit)).fst _ _ = _
    rw [hsome]

/-- `isautom` returns `true` exactly when every edge maps to an edge
under `γ`: the loop's specification, consumable with the `rowsOf`
dischargers. -/
theorem isautom_iff (ctx : Ctx n) (γ : Array Nat) :
    isautom ctx γ = true ↔
      ∀ i < n, ∀ pos ∈ ctx.g[i]!.toList,
        pos > i → ctx.g[γ[i]!]!.mem γ[pos]! = true := by
  rw [isautom_eq_scan]
  have hcases := forIn_scan_fst_cases (List.range n)
    (isautomOuter ctx γ) (isautomPass ctx γ)
    (isautomOuter_gate ctx γ)
  have hiff := forIn_scan_fst_eq_none (List.range n)
    (isautomOuter ctx γ) (isautomPass ctx γ)
    (isautomOuter_gate ctx γ)
  constructor
  · intro h
    intro i hi
    refine (hiff.mp ?_) i (List.mem_range.mpr hi)
    rcases hcases with hf | hf
    · exact hf
    · rw [hf] at h
      exact absurd h (by simp)
  · intro h
    have hnone : (forIn (List.range n) (none, ())
        (isautomOuter ctx γ) : Id (Option Bool × Unit)).fst = none :=
      hiff.mpr fun i hi => h i (List.mem_range.mp hi)
    rw [hnone]

/-!
**The residual gap to `certifyCanon?` totality is closed.** Beyond
layers one and two it needed the rows equality (definitional from
`produceCand`'s key), `colorSortedCheck` of the transcription's
output labelling, and layer three, the maximality of the traced key.
Layer three is `canonSpecKey_eq_tracedKey` and the assembly is
`certifyCanon?_isSome`, both in `SearchOutcomeCertify.lean`.
-/

/-! # Layer two, part b: `checkAutom` from the admission filter

`AutState.admit` verifies candidates with `isautom` (upper-triangle
edge preservation) rather than the replay's `checkAutom` (per-row
image equality). For a permutation of a symmetric, loopless, bounded
row array the two agree, by the finite counting argument: forward
edge inclusion makes each transported row a submask of the target
row, a renaming preserves per-row bit counts, and reindexing the
total bit count by the permutation forces per-row equality. -/

/-- Sums of `Nat` lists are permutation-invariant. -/
private theorem sum_perm {l₁ l₂ : List Nat} (h : l₁.Perm l₂) :
    l₁.sum = l₂.sum := by
  rw [List.sum_eq_foldr, List.sum_eq_foldr]
  exact h.foldr_eq' (fun x _ y _ z => by omega) 0

/-- Mapped sums are monotone under pointwise domination. -/
private theorem sum_map_le {f g : Nat → Nat} :
    ∀ l : List Nat, (∀ x ∈ l, f x ≤ g x) →
      (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := sum_map_le l fun x hx => h x (List.mem_cons_of_mem a hx)
    omega

/-- Pointwise domination with a dominated total is pointwise
equality. -/
private theorem map_eq_of_le_of_sum_le {f g : Nat → Nat} :
    ∀ l : List Nat, (∀ x ∈ l, f x ≤ g x) →
      (l.map g).sum ≤ (l.map f).sum → ∀ x ∈ l, f x = g x
  | [], _, _, _, hx => nomatch hx
  | a :: l, hle, hsum, x, hx => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      at hsum
    have h1 := hle a (List.mem_cons_self ..)
    have h2 := sum_map_le l fun y hy => hle y (List.mem_cons_of_mem a hy)
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · exact map_eq_of_le_of_sum_le l
        (fun y hy => hle y (List.mem_cons_of_mem a hy)) (by omega) x hx'

/-- Layer two, part b, the counting bridge: for a permutation of
`[0, n)`, the admission filter's `isautom` implies the replay's
`checkAutom`, over any symmetric, loopless, per-row-bounded row
array. The row hypotheses are discharged for `rowsOf G` by
`rowsOf_symm`, `rowsOf_loopless`, and `rowsOf_bounded`; the
permutation hypothesis is supplied at the use site in
`StoreValid.lean` by `scatter_isPerm`. -/
theorem checkAutom_of_isautom {ctx : Ctx n} {γ : Array Nat}
    (hsz : γ.size = n)
    (hperm : (((List.range n).map fun v => γ[v]!).isPerm
      (List.range n)) = true)
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (haut : isautom ctx γ = true) :
    checkAutom ctx.g γ = true := by
  have hbound : ∀ v, v < n → γ[v]! < n := by
    intro v hv
    have hmem : γ[v]! ∈ (List.range n).map fun v => γ[v]! :=
      List.mem_map.mpr ⟨v, List.mem_range.mpr hv, rfl⟩
    exact List.mem_range.mp
      ((List.isPerm_iff.mp hperm).mem_iff.mp hmem)
  have hnodup : (((List.range n).map fun v => γ[v]!)).Nodup :=
    ((List.isPerm_iff.mp hperm).symm.nodup List.nodup_range)
  have hinj : ∀ a b, a < n → b < n → γ[a]! = γ[b]! → a = b := by
    intro a b ha hb' hab
    have hga : ((List.range n).map fun v => γ[v]!)[a]! = γ[a]! := by
      rw [getElem!_pos _ _ (by simpa using ha), List.getElem_map,
        List.getElem_range]
    have hgb : ((List.range n).map fun v => γ[v]!)[b]! = γ[b]! := by
      rw [getElem!_pos _ _ (by simpa using hb'), List.getElem_map,
        List.getElem_range]
    exact (List.Nodup.getElem!_inj (by simpa using ha)
      (by simpa using hb') hnodup).mp (by rw [hga, hgb]; exact hab)
  have hσ : ∀ w, w < n →
      (renamingOfArray γ n hbound hinj) w = γ[w]! := by
    intro w hw
    show (if w < n then γ[w]! else w) = γ[w]!
    rw [ite_eq_left hw]
  have himg : ∀ s : VSet n, s.image (fun w => γ[w]!) =
      s.image (renamingOfArray γ n hbound hinj) :=
    fun s => image_congr s fun v hv => (hσ v hv).symm
  have hia := (isautom_iff ctx γ).mp haut
  have hedge : ∀ i pos, i < n → pos < n →
      (ctx.g[i]!).mem pos = true →
      (ctx.g[γ[i]!]!).mem γ[pos]! = true := by
    intro i pos hi hpos hbit
    rcases Nat.lt_trichotomy i pos with hlt | heq | hgt
    · exact hia i hi pos (mem_toList.mpr ⟨hpos, hbit⟩) hlt
    · subst heq
      rw [hloop i hi] at hbit
      exact Bool.noConfusion hbit
    · have hbit' : (ctx.g[pos]!).mem i = true := by
        rw [← hsymm i pos hi hpos]
        exact hbit
      have h2 := hia pos hpos i (mem_toList.mpr ⟨hi, hbit'⟩) hgt
      rw [hsymm (γ[i]!) (γ[pos]!) (hbound i hi) (hbound pos hpos)]
      exact h2
  have hsub : ∀ v, v < n →
      (ctx.g[v]!.image (fun w => γ[w]!)).subset ctx.g[γ[v]!]! = true := by
    intro v hv
    refine VSet.subset_iff.mpr fun w hw => ?_
    rw [VSet.mem_image, List.any_eq_true] at hw
    obtain ⟨u, hu, hc⟩ := hw
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rw [← hc.1.2]
    exact hedge v u hv (List.mem_range.mp hu) hc.1.1
  have hbc_img : ∀ s : VSet n, (s.image (fun w => γ[w]!)).card = s.card := by
    intro s
    rw [himg, VSet.card_image]
  have hbc_le : ∀ v, v < n → ctx.g[v]!.card ≤ ctx.g[γ[v]!]!.card := by
    intro v hv
    rw [← hbc_img ctx.g[v]!]
    exact VSet.card_le_of_subset (hsub v hv)
  have hsum : (((List.range n).map fun v => ctx.g[γ[v]!]!.card)).sum =
      (((List.range n).map fun v => ctx.g[v]!.card)).sum := by
    have hp : ((List.range n).map fun v => ctx.g[γ[v]!]!.card).Perm
        ((List.range n).map fun v => ctx.g[v]!.card) := by
      have hpm := (List.isPerm_iff.mp hperm).map fun u => ctx.g[u]!.card
      rw [List.map_map] at hpm
      exact hpm
    exact sum_perm hp
  have heq_bc := map_eq_of_le_of_sum_le (List.range n)
    (fun v hv => hbc_le v (List.mem_range.mp hv)) (Nat.le_of_eq hsum)
  have hrow : ∀ v, v < n →
      ctx.g[v]!.image (fun w => γ[w]!) = ctx.g[γ[v]!]! := by
    intro v hv
    refine VSet.eq_of_subset_of_card_eq (hsub v hv) ?_
    rw [hbc_img ctx.g[v]!]
    exact heq_bc v (List.mem_range.mpr hv)
  rw [checkAutom]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using hsz, ?_⟩, hperm⟩, ?_⟩
  · exact List.all_eq_true.mpr fun v hv => by
      simpa using hbound v (List.mem_range.mp hv)
  · refine List.all_eq_true.mpr fun v hv => ?_
    simp only [beq_iff_eq]
    exact (hrow v (List.mem_range.mp hv)).symm

/-! # Layer two, part b: the validated-store invariant

Every generator pair the producer stores passes `checkAutom`: the
stored generator via the admission filter's `isautom` plus the
counting bridge, the stored inverse via `checkAutom_invPerm`. The
permutation side of each candidate enters as a hypothesis on the
admitted candidate.

The landed totality proof does not go through this invariant.
`CertStore.lean` establishes store validity structurally over the
emitted certificate instead; what follows states the search-side
invariant. -/

/-- The store invariant: every stored generator pair passes
`checkAutom` in both components. -/
def GensOk (ctx : Ctx n) (st : AutState) : Prop :=
  ∀ p ∈ st.gens, checkAutom ctx.g p.1 = true ∧
    checkAutom ctx.g p.2 = true

/-- Admission preserves the store invariant: the filter re-verifies
size, bounds, and `isautom`, so with the candidate's permutation
side (hypothesis `hγ`) the counting bridge validates the stored
pair. -/
theorem GensOk.admit {ctx : Ctx n} {st : AutState} {γ : Array Nat}
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (hγ : isautom ctx γ = true →
      (((List.range n).map fun v => γ[v]!).isPerm
        (List.range n)) = true)
    (hst : GensOk ctx st) : GensOk ctx (st.admit ctx γ) := by
  have hpair : ((γ.size == n &&
        (List.range n).all fun v => decide (γ[v]! < n)) &&
        isautom ctx γ) = true →
      checkAutom ctx.g γ = true ∧
        checkAutom ctx.g (invPerm γ) = true := by
    intro hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hA := checkAutom_of_isautom hc.1.1 (hγ hc.2) hsymm hloop hc.2
    exact ⟨hA, checkAutom_invPerm hA⟩
  rw [AutState.admit]
  simp only [Id.run, pure]
  repeat' split
  all_goals intro p hp
  all_goals first
    | exact hst p hp
    | · rename_i hc _
        simp only at hp
        rcases Array.mem_push.mp hp with hmem | rfl
        · exact hst p hmem
        · exact hpair hc
    | · rename_i hc _ _
        simp only at hp
        rw [Array.mem_def, Array.set!_eq_setIfInBounds,
          Array.toList_setIfInBounds] at hp
        rcases List.mem_or_eq_of_mem_set hp with hmem | rfl
        · exact hst p (Array.mem_def.mpr hmem)
        · exact hpair hc

/-- A fold preserves any invariant its step preserves on the list's
elements. -/
theorem foldl_preserves_mem {α σ : Type} (P : σ → Prop) (g : σ → α → σ) :
    ∀ (l : List α), (∀ s a, a ∈ l → P s → P (g s a)) →
      ∀ (s : σ), P s → P (l.foldl g s)
  | [], _, _, hs => hs
  | a :: t, h, s, hs => foldl_preserves_mem P g t
      (fun s' a' ha' => h s' a' (List.mem_cons_of_mem a ha'))
      (g s a) (h s a (List.mem_cons_self ..) hs)

/-- The fresh store is trivially valid. -/
theorem GensOk.init (ctx : Ctx n) (nn : Nat) (budget : Option Nat) :
    GensOk ctx (AutState.init nn budget) := by
  intro p hp
  simp [AutState.init] at hp

/-- Layer two, part b, the validated-store invariant: an admission
fold over candidates that are permutations whenever they pass the
admission filter (hypothesis `hautos`) stores only
`checkAutom`-valid generator pairs. -/
theorem GensOk.foldl_admit {ctx : Ctx n} {st : AutState}
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    {autos : List (Array Nat)}
    (hautos : ∀ γ ∈ autos, isautom ctx γ = true →
      (((List.range n).map fun v => γ[v]!).isPerm
        (List.range n)) = true)
    (hst : GensOk ctx st) :
    GensOk ctx (autos.foldl (fun st γ => st.admit ctx γ) st) :=
  foldl_preserves_mem (GensOk ctx) (fun st γ => st.admit ctx γ) autos
    (fun _ γ hγ hs => GensOk.admit hsymm hloop (hautos γ hγ) hs)
    st hst

/-! # Layer two, part b: witness validity

`witness?` composes filtered generators breadth-first from the
identity; over a store of `checkAutom`-valid pairs every composed
witness is `checkAutom`-valid, by a queue invariant over the closure
toolkit (`checkAutom_range`, `checkAutom_compose`). The loop body is
restated with the named core matchers (`witness?.match_*`), the same
technique as `isautomOuter` above. -/

/-- The state a `ForInStep` carries, whichever constructor. -/
private def stepState {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

/-- A `forIn` over `Id` preserves any invariant its body preserves on
the list's elements. -/
private theorem forIn_id_inv {α β : Type} {P : β → Prop}
    {f : α → β → Id (ForInStep β)} :
    ∀ (l : List α),
      (∀ a ∈ l, ∀ b, P b → P (stepState (f a b))) →
      ∀ (b : β), P b → P (forIn l b f : Id β)
  | [], _, _, hb => hb
  | a :: as, h, b, hb => by
    rw [List.forIn_cons]
    have hstep := h a (List.mem_cons_self ..) b hb
    rcases hf : f a b with b' | b'
    · rw [hf] at hstep
      exact hstep
    · rw [hf] at hstep
      exact forIn_id_inv as
        (fun a' ha' => h a' (List.mem_cons_of_mem a ha')) b' hstep

/-- The outer loop body of `witness?`, spelled with the named core
matchers so it is definitionally identical to the `do`-desugaring. -/
private def witnessOuter (rsLab : Array Nat) (tc o : Nat)
    (usable : Array (Array Nat × Array Nat)) (_x : Nat)
    (__s : Option (Option (Nat × Array Nat)) ×
      Array (Nat × Array Nat) × VSet n × Nat) :
    Id (ForInStep (Option (Option (Nat × Array Nat)) ×
      Array (Nat × Array Nat) × VSet n × Nat)) :=
  have __s := __s.snd
  have queue := __s.fst
  have __s := __s.snd
  have seen := __s.fst
  have head := __s.snd
  if head < queue.size then
    witness?.match_5
      (fun _ => Id (ForInStep (Option (Option (Nat × Array Nat)) ×
        Array (Nat × Array Nat) × VSet n × Nat)))
      queue[head]! fun u π =>
      have head := head + 1
      have hit := none
      do
      let __s ←
        forIn [0:o] hit fun j __s =>
            have hit := __s
            if (rsLab[tc + j]! == u) = true then
              have hit := some j
              pure (ForInStep.yield hit)
            else pure (ForInStep.yield hit)
      have hit : Option Nat := __s
      witness?.match_1
          (fun _ => Id (ForInStep (Option (Option (Nat × Array Nat)) ×
            Array (Nat × Array Nat) × VSet n × Nat)))
          hit (fun o' => pure (ForInStep.done
            (some (some (o', π)), queue, seen, head))) fun _ => do
          let __s ←
            forIn usable (queue, seen) fun x __s =>
                have queue := __s.fst
                have seen := __s.snd
                witness?.match_3
                  (fun _ => Id (ForInStep (Array (Nat × Array Nat) × VSet n)))
                  x fun γ γi => do
                  let __s ←
                    forIn [γ, γi] (queue, seen) fun f __s =>
                        have queue := __s.fst
                        have seen := __s.snd
                        have w := f[u]!
                        if seen.mem w = true then
                          pure (ForInStep.yield (queue, seen))
                        else
                          have seen := seen.insert w
                          have queue := queue.push (w, composePerm f π n)
                          pure (ForInStep.yield (queue, seen))
                  have queue : Array (Nat × Array Nat) := __s.fst
                  have seen : VSet n := __s.snd
                  pure (ForInStep.yield (queue, seen))
          have queue : Array (Nat × Array Nat) := __s.fst
          have seen : VSet n := __s.snd
          pure (ForInStep.yield (none, queue, seen, head))
  else pure (ForInStep.yield (none, queue, seen, head))

private theorem witness?_eq (rsLab : Array Nat) (tc : Nat)
    (usable : Array (Array Nat × Array Nat)) (o : Nat) :
    witness? n rsLab tc usable o =
      if (o == 0 || usable.isEmpty) = true then none
      else
        Break.runK.match_1 (fun _ => Id (Option (Nat × Array Nat)))
          (forIn [0:n]
            ((none : Option (Option (Nat × Array Nat))),
              #[(rsLab[tc + o]!, Array.range n)],
              VSet.empty.insert rsLab[tc + o]!, (0 : Nat))
            (witnessOuter rsLab tc o usable) :
              Id (Option (Option (Nat × Array Nat)) ×
                Array (Nat × Array Nat) × VSet n × Nat)).fst
          (fun r => pure r) (fun _ => pure none) := by
  rw [witness?]
  rfl

private theorem id_bind_eq {α β : Type} (x : Id α) (f : α → Id β) :
    x >>= f = f x := rfl

/-- The witness-queue invariant: every queued composition, and any
returned witness, passes `checkAutom`. -/
private def WitnessInv (ctx : Ctx n)
    (s : Option (Option (Nat × Array Nat)) ×
      Array (Nat × Array Nat) × VSet n × Nat) : Prop :=
  (∀ q ∈ s.2.1, checkAutom ctx.g q.2 = true) ∧
  (∀ a b, s.1 = some (some (a, b)) → checkAutom ctx.g b = true)

private theorem witnessOuter_inv {ctx : Ctx n} {rsLab : Array Nat}
    {tc o : Nat} {usable : Array (Array Nat × Array Nat)}
    (hu : ∀ p ∈ usable, checkAutom ctx.g p.1 = true ∧
      checkAutom ctx.g p.2 = true)
    (x : Nat)
    (s : Option (Option (Nat × Array Nat)) ×
      Array (Nat × Array Nat) × VSet n × Nat)
    (hs : WitnessInv ctx s) :
    WitnessInv ctx
      (stepState (witnessOuter rsLab tc o usable x s)) := by
  rw [witnessOuter]
  dsimp only
  split
  case isFalse => exact ⟨hs.1, fun a b h => nomatch h⟩
  case isTrue hlt =>
    have hπ : checkAutom ctx.g (s.2.1[s.2.2.2]!).2 = true := by
      have hq : s.2.1[s.2.2.2]! ∈ s.2.1 := by
        rw [getElem!_pos s.2.1 s.2.2.2 hlt]
        exact Array.getElem_mem hlt
      exact hs.1 _ hq
    simp only [id_bind_eq]
    split
    · exact ⟨hs.1, fun a b h => by
        injection h with h1
        injection h1 with h2
        injection h2 with h3 h4
        rw [← h4]
        exact hπ⟩
    · refine ⟨?_, fun a b h => nomatch h⟩
      rw [← Array.forIn_toList]
      refine forIn_id_inv
        (P := fun qs : Array (Nat × Array Nat) × VSet n =>
          ∀ q ∈ qs.1, checkAutom ctx.g q.2 = true)
        usable.toList ?_ (s.2.1, s.2.2.1) hs.1
      intro p hp qs hqs
      refine forIn_id_inv
        (P := fun qs : Array (Nat × Array Nat) × VSet n =>
          ∀ q ∈ qs.1, checkAutom ctx.g q.2 = true)
        [p.1, p.2] ?_ qs hqs
      intro f hf qs2 hqs2
      have hf' : checkAutom ctx.g f = true := by
        have hp' := hu p (Array.mem_toList_iff.mp hp)
        rcases List.mem_cons.mp hf with rfl | hf2
        · exact hp'.1
        · have hfi : f = p.2 := by simpa using hf2
          rw [hfi]
          exact hp'.2
      split
      · exact hqs2
      · intro q hq
        rcases Array.mem_push.mp hq with hmem | rfl
        · exact hqs2 q hmem
        · exact checkAutom_compose hf' hπ

/-- Layer two, part b, witness validity: over a store of
`checkAutom`-valid generator pairs, every witness `witness?` returns
passes `checkAutom` — the breadth-first queue holds only the identity
and `checkAutom`-closed compositions. -/
theorem witness?_checkAutom {ctx : Ctx n} {rsLab : Array Nat}
    {tc o : Nat} {usable : Array (Array Nat × Array Nat)}
    {o' : Nat} {π : Array Nat}
    (hu : ∀ p ∈ usable, checkAutom ctx.g p.1 = true ∧
      checkAutom ctx.g p.2 = true)
    (hw : witness? n rsLab tc usable o = some (o', π)) :
    checkAutom ctx.g π = true := by
  rw [witness?_eq] at hw
  by_cases h0 : (o == 0 || usable.isEmpty) = true
  · rw [ite_eq_left h0] at hw
    exact nomatch hw
  · rw [ite_eq_right h0, forIn_range_eq] at hw
    have hinit : WitnessInv ctx
        ((none : Option (Option (Nat × Array Nat))),
          #[(rsLab[tc + o]!, Array.range n)],
          VSet.empty.insert rsLab[tc + o]!, (0 : Nat)) := by
      constructor
      · intro q hq
        have hq' : q = (rsLab[tc + o]!, Array.range n) := by
          simpa using hq
        rw [hq']
        exact checkAutom_range
      · intro a b h
        exact nomatch h
    have hinv := forIn_id_inv (f := witnessOuter rsLab tc o usable)
      (List.range n)
      (fun x _ s hs => witnessOuter_inv hu x s hs) _ hinit
    rcases hfst : (forIn (List.range n)
        ((none : Option (Option (Nat × Array Nat))),
          #[(rsLab[tc + o]!, Array.range n)],
          VSet.empty.insert rsLab[tc + o]!, (0 : Nat))
        (witnessOuter rsLab tc o usable) :
          Id (Option (Option (Nat × Array Nat)) ×
            Array (Nat × Array Nat) × VSet n × Nat)).fst with _ | r
    · rw [hfst] at hw
      have hcon : (none : Option (Nat × Array Nat)) = some (o', π) := hw
      exact nomatch hcon
    · rw [hfst] at hw
      have hr : r = some (o', π) := hw
      exact hinv.2 o' π (by rw [hfst, hr])

end Hex.GraphIso.Nauty
