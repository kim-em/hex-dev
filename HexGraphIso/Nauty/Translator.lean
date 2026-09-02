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
composed from individually-valid generators is itself valid. The full
layer-two statement — the emitted certificate replays — is
conditional on key domination (no visited subtree exceeds the claimed
key), which is layer three's content; the conditional spine and its
remaining obligations are inventoried at the end of this file.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-! # Layer one: total production under an absent budget -/

theorem charge_of_budget_none {st : AutState}
    (h : st.budget = none) : st.charge = st := by
  rw [AutState.charge, h]

theorem admit_budget (ctx : Ctx) (st : AutState) (γ : Array Nat) :
    (st.admit ctx γ).budget = st.budget := by
  rw [AutState.admit]
  simp only [Id.run, pure]
  repeat' split
  all_goals rfl

theorem admit_exhausted (ctx : Ctx) (st : AutState) (γ : Array Nat) :
    (st.admit ctx γ).exhausted = st.exhausted := by
  rw [AutState.admit]
  simp only [Id.run, pure]
  repeat' split
  all_goals rfl

theorem harvest_budget (ctx : Ctx) (st : AutState) (lab : Array Nat) :
    (st.harvest ctx lab).budget = st.budget := by
  rw [AutState.harvest]
  simp only [Id.run, pure]
  repeat' split
  all_goals simp only [admit_budget]

theorem harvest_exhausted (ctx : Ctx) (st : AutState)
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

theorem certifyNodeAutom_budget (ctx : Ctx) (tcLevel : Nat) :
    ∀ (fuel level : Nat) (lab ptn : Array Nat)
      (active numcells : Nat) (bcodes : List Nat) (st : AutState),
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
    (fun st γ => st.admit { n := n, g := rowsOf G } γ)
    (fun st γ hst => ⟨(admit_budget ..).trans hst.1,
      (admit_exhausted ..).trans hst.2⟩)
    (runColoredTraced G).autos.toList
    (AutState.init n none) ⟨rfl, rfl⟩
  rw [Array.foldl_toList] at hfold
  have hcert := certifyNodeAutom_budget { n := n, g := rowsOf G } 100
    n 1 (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2)
    (initActive (initialPartition G).2)
    (initialPartition G).2.length
    (achieverCodes { n := n, g := rowsOf G } 100
        (runColoredTraced G).result.canonlab (n + 2) 1
        (initialPartition G).1
        (initPtn n (n + 2) (initialPartition G).2)
        (initActive (initialPartition G).2)
        (initialPartition G).2.length ++ [codeSentinel])
    { (runColoredTraced G).autos.foldl
        (fun st γ => st.admit { n := n, g := rowsOf G } γ)
        (AutState.init n none) with
      refLeaf := some (runColoredTraced G).result.canonlab }
    hfold.1
  simp only [produceCand, Option.any]
  rw [ite_eq_right (by simp)]
  rw [hcert.2]
  have hex : ({ (runColoredTraced G).autos.foldl
      (fun st γ => st.admit { n := n, g := rowsOf G } γ)
      (AutState.init n none) with
    refLeaf := some (runColoredTraced G).result.canonlab } :
      AutState).exhausted = false := hfold.2
  rw [hex]
  rfl

/-! # Graph facts for `rowsOf`: dischargers for the row-set hypotheses

The eventual `checkAutom_of_isautom` bridge is stated graph-agnostically
over a row array with symmetry, looplessness, and per-row bounds; these
lemmas discharge those hypotheses for `rowsOf G`. -/

theorem rowsOf_bounded {k : Nat} (G : Colored n k) :
    ∀ v, v < n → (rowsOf G)[v]! < 2 ^ n := by
  intro v hv
  rw [getElem!_rowsOf G hv]
  exact rowOf_lt G v

theorem rowsOf_symm {k : Nat} (G : Colored n k) :
    ∀ i j, i < n → j < n →
      ((rowsOf G)[i]!).testBit j = ((rowsOf G)[j]!).testBit i := by
  intro i j hi hj
  rw [getElem!_rowsOf G hi, getElem!_rowsOf G hj,
    testBit_rowOf_lt G hi hj, testBit_rowOf_lt G hj hi,
    G.graph.adj_symm ⟨i, hi⟩ ⟨j, hj⟩]

theorem rowsOf_loopless {k : Nat} (G : Colored n k) :
    ∀ i, i < n → ((rowsOf G)[i]!).testBit i = false := by
  intro i hi
  rw [getElem!_rowsOf G hi, testBit_rowOf_lt G hi hi,
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
theorem image_comp (σ τ : Nat → Nat) (s : Nat)
    (hτ : ∀ v, v < n → τ v < n) :
    image (fun w => σ (τ w)) n s = image σ n (image τ n s) := by
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_image, testBit_image]
  rcases hL : (List.range n).any fun v =>
      s.testBit v && σ (τ v) == w with _ | _
  · rcases hR : (List.range n).any fun u =>
        (image τ n s).testBit u && σ u == w with _ | _
    · rfl
    · exfalso
      obtain ⟨u, hu, hcond⟩ := List.any_eq_true.mp hR
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rw [testBit_image] at hcond
      obtain ⟨v, hv, hvc⟩ := List.any_eq_true.mp hcond.1
      simp only [Bool.and_eq_true, beq_iff_eq] at hvc
      have : (List.range n).any (fun v =>
          s.testBit v && σ (τ v) == w) = true :=
        List.any_eq_true.mpr ⟨v, hv, by
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨hvc.1, by rw [hvc.2]; exact hcond.2⟩⟩
      rw [hL] at this
      exact Bool.noConfusion this
  · obtain ⟨v, hv, hcond⟩ := List.any_eq_true.mp hL
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    refine (List.any_eq_true.mpr ⟨τ v, ?_, ?_⟩).symm
    · exact List.mem_range.mpr (hτ v (List.mem_range.mp hv))
    · simp only [Bool.and_eq_true, beq_iff_eq]
      refine ⟨?_, hcond.2⟩
      rw [testBit_image]
      exact List.any_eq_true.mpr ⟨v, hv, by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨hcond.1, trivial⟩⟩

/-- `checkAutom` is closed under the producer's witness
composition. -/
theorem checkAutom_compose {g f π : Array Nat}
    (hf : checkAutom g f n = true) (hπ : checkAutom g π n = true) :
    checkAutom g (composePerm f π n) n = true := by
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
    exact (image_congr _ fun w hw => (hχ w hw).symm) ▸ rfl

/-- The identity image of a bounded set is itself. -/
theorem image_id_of_lt {s : Nat} (hs : s < 2 ^ n) :
    image (fun w => w) n s = s := by
  refine Nat.eq_of_testBit_eq fun w => ?_
  rw [testBit_image]
  rcases hw : s.testBit w with _ | _
  · rcases hL : (List.range n).any fun v =>
        s.testBit v && v == w with _ | _
    · rfl
    · obtain ⟨v, _, hc⟩ := List.any_eq_true.mp hL
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      rw [hc.2] at hc
      exact absurd hc.1 (by rw [hw]; exact Bool.false_ne_true)
  · exact List.any_eq_true.mpr ⟨w,
      List.mem_range.mpr (lt_of_testBit_of_lt hs hw), by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨hw, trivial⟩⟩

/-- `checkAutom` is closed under inversion, for bounded row sets. -/
theorem checkAutom_invPerm {g γ : Array Nat}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n)
    (hγ : checkAutom g γ n = true) :
    checkAutom g (invPerm γ) n = true := by
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
    have : image (fun w => (invPerm γ)[γ[w]!]!) n g[v]! =
        image (fun w => w) n g[v]! :=
      image_congr _ fun w hw => hδγ w hw
    rw [this, image_id_of_lt (hb v hvn)]

/-- The identity array is a checked automorphism of any graph with
bounded rows: the base case of witness composition. -/
theorem checkAutom_range {g : Array Nat}
    (hb : ∀ v, v < n → g[v]! < 2 ^ n) :
    checkAutom g (Array.range n) n = true := by
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
    have : image (fun w => (Array.range n)[w]!) n g[v]! =
        image (fun w => w) n g[v]! :=
      image_congr _ fun w hw => hget w hw
    rw [hget v hvn, this, image_id_of_lt (hb v hvn)]

/-!
# Inventory: the remaining layer-two and layer-three obligations

Everything below is stated for the record and not yet proven; the
statements were validated against the current definitions.

**Store invariant (layer two, part b).** Every generator pair the
producer stores satisfies `checkAutom` for both components. Two
findings from validating this statement against `AutState.admit`:
the admission filter checks size, bounds, and `isautom` but not
injectivity, so the invariant is conditional on admitted candidates
being permutations; and `isautom` (edge-preservation checked from the
lesser endpoint) implies the row-image equality of `checkAutom` only
through a finite-injection counting argument. The two missing
bridges, as statements:

* `isPerm_of_trace`: every `γ` in `(runColoredTraced G).autos`, and
  every `composeOnto` of two leaf labellings of the certify walk, is
  a permutation of `[0, n)` — the former is a property of the
  transcription (layer-four-adjacent), the latter follows from
  `LabOk` preservation along the walk.
* `checkAutom_of_isautom`: for a permutation `γ` of `[0, n)` with
  `isautom ctx γ = true`, `checkAutom ctx.g γ ctx.n = true` — the
  edges-to-edges injection on a finite edge set is a bijection, so
  rows map onto rows. Stated graph-agnostically it takes row-set
  hypotheses (`γ` permutes and is bounded; `ctx.g` is symmetric,
  loopless, and per-row `< 2 ^ n`) discharged for `rowsOf G` by
  `rowsOf_symm`/`rowsOf_loopless`/`rowsOf_bounded` above.

  Refined decomposition (this fork's findings — `checkAutom_of_isautom`
  is itself directive-sized, not a session sub-step):

  1. `isautom_sound`: the do-notation spec. `isautom` is a nested
     `Std.Range.forIn` with early `return false` and there is no
     spec-lemma precedent for that shape anywhere in the tree, so this
     is a from-scratch loop-invariant proof yielding
     `isautom ctx γ = true → ∀ i pos, i < n → pos < n → i < pos →
     (g[i]!).testBit pos → (g[γ[i]!]!).testBit (γ[pos]!)`.
  2. Forward inclusion (tractable given 1): `image (fun w => γ[w]!) n
     g[v]! ⊆ g[γ[v]!]!` as a submask, from `isautom_sound` +
     `rowsOf_symm` (to cover `pos < i`) + `rowsOf_loopless` (to rule
     out `pos = i`) via `testBit_image`.
  3. The counting core. Forward inclusion plus vertex-bijection does
     NOT give the reverse inclusion; it needs the finite edge-set
     cardinality argument, and none of its ingredients exist yet:
     `popCount` monotonicity under submask, `submask + equal popCount
     ⇒ equal` (both `< 2 ^ n`), and `∑_{v<n} popCount g[v]! =
     ∑_{v<n} popCount g[γ[v]!]!` by reindexing `γ` over `[0, n)`. With
     `popCount_image` (cardinality preserved by the `renamingOfArray`
     of `γ`) these close the reverse inclusion. This sub-toolkit is
     the bulk of the lemma and should be its own directive.

With those, the store invariant follows by `foldl_preserves` over
admissions, and witness validity (`witness?` returns only
`checkAutom`-valid arrays) follows from `checkAutom_range`,
`checkAutom_compose`, and `checkAutom_invPerm` by an invariant on the
breadth-first queue.

**The conditional spine (layer two, part c).** The issue's
unconditional claim is unsound: `certifyNodeAutom` emits
`.codePrune` on the `.gt` comparison, which the replay rejects, and a
`.leaf` whose key exceeds the claimed suffix likewise fails
`keyCmp`. The honest statement is conditional on key domination:

* `certify_replays_of_dominated`: if every node visited by the walk
  has `rs.longcode ≤` the claimed code at its depth and every leaf
  key is `≤ ⟨bcodes, brows⟩` (the `keyLe` conditions `checkNode`
  enforces), and the store invariant holds, then
  `checkNode ctx tcLevel brows (validGammas …) … (certifyNodeAutom …).1 bcodes = some a`
  for some `a`. The induction relates the walk's emission decisions
  to `checkNode`'s acceptance on identical node state; the
  `.autom` branch needs the store invariant for the `validGammas`
  membership and `childCellsOk` for the transported cells.

The domination hypothesis for the traced key is exactly layer three
(the transcription's leaf is the spec maximum).

## The guarded-scan `forIn` technique

The transcription-facing specifications — `isautom_sound` (edge
preservation from an accepted permutation) and, downstream,
`isPerm_of_trace` — reason about nested `forIn` loops over `[0, n)`
with an early `return false`, a loop shape with no reasoning
precedent in the tree. The reusable technique is a "guarded scan"
whose state is `Option Bool × Unit`: it yields `(none, ())` while
every element passes and is done with `(some false, ())` on the first
failure, so the result flag is `none` exactly when every element
passes (`forIn_scan_fst_cases`, `forIn_scan_fst_eq_none`), with
`forIn_range_eq` and `id_run_scan` reducing the `[0, n)` range and the
outer `Id` do-block. The lemma family is staged here for those
consumers; connecting it to a concrete `isautom` obligation is the
open step (the hand-abstracted scan body is definitionally equal to
the desugaring but not `rw`-matchable to it, which needs either a
direct `List.forIn` induction on the reduced hypothesis or a core
`forIn`-to-`List.all` characterization).

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

/-- Membership in `toList s n`. -/
private theorem mem_toList {s n pos : Nat} :
    pos ∈ toList s n ↔ pos < n ∧ s.testBit pos = true := by
  rw [toList, List.mem_filter, List.mem_range]

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

/-!
**Residual gap to `certifyCanon?` totality.** With layers one and
two, `(Nauty.certifyCanon? G).isSome` additionally needs:

* rows equality — `B.rows = leafRows ctx canonlab` holds by
  construction of `produceCand`'s key (definitional);
* `colorSortedCheck G (runColored G).canonlab = true` — a property
  of the transcribed search's output labelling;
* layer three — `⟨achieverCodes … ++ [codeSentinel], leafRows ctx canonlab⟩ = canonSpecKey G`,
  the maximality of the traced key, which also discharges the
  domination hypothesis above.
-/

end Hex.GraphIso.Nauty
