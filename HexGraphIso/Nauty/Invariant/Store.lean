/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Cert.Translator
public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Search.Search

public section

/-!
Store validity: every generator `processnode` admits passes
`checkAutom`, per admission arm and as the `GenTraceOk` invariant
the domination induction threads.
-/

/-!
Store validity for the admitted automorphisms (SPEC § Verified search
refinement, the replay hypothesis's store-validity clause).

The traced run's `genTrace` feeds the certificate producer: every
`.autom` record carries one of its entries, and the replay's
`validGammas` keeps only entries passing `checkAutom`, so a replayed
certificate needs every admitted entry to pass.

Both admission sites in `processnode` push the same shape of array: a
scatter `γ` with `γ[lab₁[i]!]! = lab₂[i]!` connecting two discrete
leaf labellings (code 1 scatters `lab` over `firstlab`, code 2
scatters `lab` over `canonlab`). The lemmas below prove the per-admission
facts about that shape: `scatter_isPerm` shows a scatter of one
permutation labelling over another is itself a permutation of
`[0, n)`; `checkAutom_scatter_of_isautom` closes the code-1 arm under
its explicit `isautom` guard; and `checkAutom_scatter_of_leafRows_eq`
closes the code-2 arm outright, with no `isautom` scan: the
`testcanlab` equality outcome (transported to `leafRows` equality by
`leafEvent_faithful` and `updatecan_inv`) means the two relabelled
graphs coincide, which forces the connecting scatter to preserve
every row.

The code-1 arm's other guard, `gcaFirst ≥ noncheaplevel` with no
`isautom` scan, admits on the strength of `cheapautom`: an equitable
partition whose nontrivial cells are small enough forces every leaf
below to realize an automorphism. That argument needs a theory of
equitable partitions the development does not yet have; the theorems
here are stated so that arm can slot in beside them once proven.
-/

namespace Hex.GraphIso.Nauty

variable {nn : Nat}

/-- Entries of a permutation labelling are vertices. -/
private theorem perm_getElem!_lt {lab : Array Nat}
    (hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn))
    {i : Nat} (hi : i < nn) : lab[i]! < nn := by
  have hmem : lab[i]! ∈ lab.toList := by
    rw [getElem!_pos lab i (by omega)]
    exact List.getElem_mem (by simpa [hsz] using hi)
  exact List.mem_range.mp (hp.mem_iff.mp hmem)

/-- A permutation labelling attains every vertex. -/
private theorem perm_surj {lab : Array Nat}
    (hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn))
    {v : Nat} (hv : v < nn) : ∃ i, i < nn ∧ lab[i]! = v := by
  have hmem : v ∈ lab.toList := hp.mem_iff.mpr (List.mem_range.mpr hv)
  obtain ⟨i, hi, hei⟩ := List.getElem_of_mem hmem
  refine ⟨i, by simpa [hsz] using hi, ?_⟩
  rw [getElem!_pos lab i (by simpa using hi)]
  simpa using hei

/-- A permutation labelling is injective on positions. -/
private theorem perm_inj {lab : Array Nat}
    (_hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn)) :
    ∀ a b, a < lab.size → b < lab.size → lab[a]! = lab[b]! → a = b := by
  intro a b ha hb hab
  have hnodup : lab.toList.Nodup := hp.symm.nodup List.nodup_range
  have hla : lab.toList[a]! = lab[a]! := by
    rw [getElem!_pos lab a ha, getElem!_pos _ a (by simpa using ha)]
    simp
  have hlb : lab.toList[b]! = lab[b]! := by
    rw [getElem!_pos lab b hb, getElem!_pos _ b (by simpa using hb)]
    simp
  exact (List.Nodup.getElem!_inj (by simpa using ha)
    (by simpa using hb) hnodup).mp (by rw [hla, hlb]; exact hab)

/-- The positions-to-entries map of a sized array, as a list. -/
private theorem map_range_getElem! {lab : Array Nat}
    (hsz : lab.size = nn) :
    ((List.range nn).map fun i => lab[i]!) = lab.toList := by
  refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos lab i (by simpa using h2)]
  simp

/-- The scatter of one permutation labelling over another is a
permutation of `[0, n)`: the `isPerm` side condition that
`checkAutom_of_isautom` consumes, produced from the two labellings'
permutation properties. -/
theorem scatter_isPerm {γ lab₁ lab₂ : Array Nat}
    (hsz₁ : lab₁.size = nn) (hp₁ : lab₁.toList.Perm (List.range nn))
    (hsz₂ : lab₂.size = nn) (hp₂ : lab₂.toList.Perm (List.range nn))
    (hsc : ∀ i, i < nn → γ[lab₁[i]!]! = lab₂[i]!) :
    (((List.range nn).map fun v => γ[v]!).isPerm (List.range nn)) =
      true := by
  rw [List.isPerm_iff]
  have h1 : ((List.range nn).map fun v => γ[v]!).Perm
      (lab₁.toList.map fun v => γ[v]!) := (hp₁.map _).symm
  have h2 : (lab₁.toList.map fun v => γ[v]!) =
      (List.range nn).map fun i => γ[lab₁[i]!]! := by
    rw [← map_range_getElem! hsz₁, List.map_map]
    rfl
  have h3 : ((List.range nn).map fun i => γ[lab₁[i]!]!) =
      (List.range nn).map fun i => lab₂[i]! :=
    List.map_congr_left fun i hi => hsc i (List.mem_range.mp hi)
  refine (h1.trans ?_)
  rw [h2, h3, map_range_getElem! hsz₂]
  exact hp₂

/-- The code-1 admission under its explicit `isautom` guard: the
scatter of the leaf labelling over the first-path labelling passes
`checkAutom` when the `isautom` scan accepted it. -/
theorem checkAutom_scatter_of_isautom {ctx : Ctx n}
    {γ lab₁ lab₂ : Array Nat} (hγsz : γ.size = n)
    (hsz₁ : lab₁.size = n)
    (hp₁ : lab₁.toList.Perm (List.range n))
    (hsz₂ : lab₂.size = n)
    (hp₂ : lab₂.toList.Perm (List.range n))
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (haut : isautom ctx γ = true) :
    checkAutom ctx.g γ = true :=
  checkAutom_of_isautom hγsz (scatter_isPerm hsz₁ hp₁ hsz₂ hp₂ hsc)
    hsymm hloop haut

/-- A labelling undoes its inverse on vertices. -/
private theorem getElem!_comp_invPerm {lab : Array Nat}
    (hsz : lab.size = nn) (hp : lab.toList.Perm (List.range nn))
    {w : Nat} (hw : w < nn) : lab[(invPerm lab)[w]!]! = w := by
  obtain ⟨j, hj, hje⟩ := perm_surj hsz hp hw
  have hinv : (invPerm lab)[lab[j]!]! = j :=
    getElem!_invPerm lab (perm_inj hsz hp) (by omega) (by rw [hje]; omega)
  rw [← hje, hinv]

/-- The scatter agrees with composition through the base's inverse. -/
private theorem scatter_eq_comp_invPerm {γ lab₁ lab₂ : Array Nat}
    (hsz₁ : lab₁.size = nn) (hp₁ : lab₁.toList.Perm (List.range nn))
    (hsc : ∀ i, i < nn → γ[lab₁[i]!]! = lab₂[i]!)
    {w : Nat} (hw : w < nn) : γ[w]! = lab₂[(invPerm lab₁)[w]!]! := by
  obtain ⟨j, hj, hje⟩ := perm_surj hsz₁ hp₁ hw
  have hinv : (invPerm lab₁)[lab₁[j]!]! = j :=
    getElem!_invPerm lab₁ (perm_inj hsz₁ hp₁) (by omega) (by rw [hje]; omega)
  rw [← hje, hinv]
  exact hsc j hj

/-- A leaf row is the row's image through the labelling's inverse. -/
private theorem leafRows_getElem! {ctx : Ctx n} {lab : Array Nat}
    {i : Nat} (hi : i < n) :
    (leafRows ctx lab)[i]! =
      ctx.g[lab[i]!]!.image (fun w => (invPerm lab)[w]!) := by
  rw [leafRows, getElem!_pos _ _ (by simpa using hi), List.getElem_map,
    List.getElem_range]
  rfl

/-- The code-2 admission: two permutation labellings presenting equal
leaf rows are joined by an automorphism, so the scatter passes
`checkAutom` with no `isautom` scan. Equal rows mean the two
relabelled graphs coincide; transporting one row identity back
through the labellings' inverses shows the scatter preserves every
row. -/
theorem checkAutom_scatter_of_leafRows_eq {ctx : Ctx n}
    {γ lab₁ lab₂ : Array Nat} (hγsz : γ.size = n)
    (hsz₁ : lab₁.size = n)
    (hp₁ : lab₁.toList.Perm (List.range n))
    (hsz₂ : lab₂.size = n)
    (hp₂ : lab₂.toList.Perm (List.range n))
    (hsc : ∀ i, i < n → γ[lab₁[i]!]! = lab₂[i]!)
    (hrows : leafRows ctx lab₁ = leafRows ctx lab₂) :
    checkAutom ctx.g γ = true := by
  have hbound : ∀ v, v < n → γ[v]! < n := by
    intro v hv
    obtain ⟨i, hi, hei⟩ := perm_surj hsz₁ hp₁ hv
    rw [← hei, hsc i hi]
    exact perm_getElem!_lt hsz₂ hp₂ hi
  have htrans : ∀ v, v < n →
      ctx.g[γ[v]!]! = ctx.g[v]!.image (fun w => γ[w]!) := by
    intro v hv
    obtain ⟨i, hi, hei⟩ := perm_surj hsz₁ hp₁ hv
    have hrow : ctx.g[lab₁[i]!]!.image (fun w => (invPerm lab₁)[w]!) =
        ctx.g[lab₂[i]!]!.image (fun w => (invPerm lab₂)[w]!) := by
      have h1 := leafRows_getElem! (ctx := ctx) (lab := lab₁) hi
      have h2 := leafRows_getElem! (ctx := ctx) (lab := lab₂) hi
      rw [← h1, ← h2, hrows]
    have hinvb₁ : ∀ w, w < n → (invPerm lab₁)[w]! < n := by
      intro w _
      have := getElem!_invPerm_lt (lab := lab₁) (by omega) w
      omega
    have hinvb₂ : ∀ w, w < n → (invPerm lab₂)[w]! < n := by
      intro w _
      have := getElem!_invPerm_lt (lab := lab₂) (by omega) w
      omega
    have hcomp₂ : (ctx.g[lab₂[i]!]!.image (fun w => (invPerm lab₂)[w]!)).image
        (fun w => lab₂[w]!) = ctx.g[lab₂[i]!]! := by
      rw [← image_comp _ _ _ hinvb₂]
      calc ctx.g[lab₂[i]!]!.image (fun w => lab₂[(invPerm lab₂)[w]!]!)
          = ctx.g[lab₂[i]!]!.image (fun w => w) :=
            image_congr _ fun w hw => getElem!_comp_invPerm hsz₂ hp₂ hw
        _ = ctx.g[lab₂[i]!]! := image_id _
    have hcomp₁ : (ctx.g[lab₁[i]!]!.image (fun w => (invPerm lab₁)[w]!)).image
        (fun w => lab₂[w]!) = ctx.g[lab₁[i]!]!.image (fun w => γ[w]!) := by
      rw [← image_comp _ _ _ hinvb₁]
      exact image_congr _ fun w hw =>
        (scatter_eq_comp_invPerm hsz₁ hp₁ hsc hw).symm
    have hγv : γ[v]! = lab₂[i]! := by
      rw [← hei]
      exact hsc i hi
    rw [hγv, ← hcomp₂, ← hrow, hcomp₁, ← hei]
  rw [checkAutom]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by simpa using hγsz, ?_⟩,
    scatter_isPerm hsz₁ hp₁ hsz₂ hp₂ hsc⟩, ?_⟩
  · exact List.all_eq_true.mpr fun v hv => by
      simpa using hbound v (List.mem_range.mp hv)
  · refine List.all_eq_true.mpr fun v hv => ?_
    simp only [beq_iff_eq]
    exact htrans v (List.mem_range.mp hv)

/-! # The admission event

`processnode` is the only search step that grows `genTrace`. The
lemmas below characterize the grown entry: the scatter loops become
folds, and the event lemma ties each push to its admission guard, in
the shape the run-level threading consumes together with the
per-admission theorems above.
-/

private theorem id_run_eq {α : Type} (x : Id α) : x.run = x := rfl

private theorem forIn_range_toList {β : Type} (n : Nat) (init : β)
    (f : Nat → β → Id (ForInStep β)) :
    (forIn [0:n] init f : Id β) = forIn (List.range n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step
      = List.range n := by simp [List.range_eq_range']
  rw [hrange]

private theorem forIn_scatter_eq (lab₁ lab₂ : Array Nat) :
    ∀ (l : List Nat) (base : Array Nat),
      (forIn l base (fun i r =>
        pure (ForInStep.yield (r.set! lab₁[i]! lab₂[i]!))) :
          Id (Array Nat)) =
      l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base
  | [], _ => rfl
  | i :: l, base => by
    rw [List.forIn_cons]
    exact forIn_scatter_eq lab₁ lab₂ l _

/-- A scatter fold preserves the size of its workspace. -/
theorem foldl_scatter_size (lab₁ lab₂ : Array Nat) :
    ∀ (l : List Nat) (base : Array Nat),
      (l.foldl (fun r i => r.set! lab₁[i]! lab₂[i]!) base).size =
        base.size
  | [], _ => rfl
  | i :: l, base => by
    rw [List.foldl_cons, foldl_scatter_size lab₁ lab₂ l,
      Array.size_set!]

/-- After scanning an injective source prefix, every scanned source slot
contains its corresponding target value. -/
theorem foldl_scatter_getElem {lab₁ lab₂ : Array Nat}
    {nn : Nat}
    (hinj : ∀ a b, a < nn → b < nn → lab₁[a]! = lab₁[b]! → a = b)
    {base : Array Nat}
    (hbb : ∀ i, i < nn → lab₁[i]! < base.size) :
    ∀ {m : Nat}, m ≤ nn → ∀ {j : Nat}, j < m →
      ((List.range m).foldl
        (fun r i => r.set! lab₁[i]! lab₂[i]!) base)[lab₁[j]!]! =
        lab₂[j]! := by
  intro m
  induction m with
  | zero => intro _ j hj; omega
  | succ p ih =>
    intro hm j hj
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rcases Decidable.em (j = p) with rfl | hne
    · rw [Array.getElem!_set!_self _ _ _
        (by rw [foldl_scatter_size]; exact hbb j (by omega))]
    · have hlne : lab₁[p]! ≠ lab₁[j]! := fun h =>
        hne (hinj j p (by omega) (by omega) h.symm)
      rw [Array.getElem!_set!_ne _ _ _ _ hlne, ih (by omega) (by omega)]

private theorem pushAuto_genTrace (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).genTrace = st.genTrace := by
  rw [pushAuto]
  split <;> rfl

/-- `processnode`'s effect on the admitted-generator trace: either
nothing is pushed, or exactly one scatter is pushed, connecting the
first-path labelling (code 1, at the recorded first-leaf depth and after
an automorphism scan) or the
incumbent labelling (code 2, under the `testcanlab` equality on the
freshly completed `canong`) to the current leaf labelling. The
injectivity and bound hypotheses on the two base labellings are
permutation facts the run-level invariant carries; the scatter
equations feed `checkAutom_scatter_of_isautom` and, through
`leafEvent_faithful`'s rows account,
`checkAutom_scatter_of_leafRows_eq`. -/
theorem processnode_genTrace {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hinj₁ : ∀ a b, a < n → b < n →
      st.firstlab[a]! = st.firstlab[b]! → a = b)
    (hb₁ : ∀ i, i < n → st.firstlab[i]! < n)
    (hinj₂ : ∀ a b, a < n → b < n →
      st.canonlab[a]! = st.canonlab[b]! → a = b)
    (hb₂ : ∀ i, i < n → st.canonlab[i]! < n) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
    ∃ γ, (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ ∧ γ.size = n ∧
      ((∀ i, i < n → γ[st.firstlab[i]!]! = st.lab[i]!) ∧
          st.firstcode[level + 1]! = codeSentinel ∧
          isautom ctx γ = true ∨
        (∀ i, i < n → γ[st.canonlab[i]!]! = st.lab[i]!) ∧
          st.compCanon = 0 ∧ st.canonlevel ≤ level ∧
          (testcanlab ctx
            (updatecan ctx st.canong st.canonlab st.samerows)
            st.lab).1 = 0) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace, ite_self]
  simp only [id_run_eq, forIn_range_toList, forIn_scatter_eq]
  rcases Decidable.em (st.eqlevFirst ≠ level ∧ st.compCanon < 0)
    with h1 | h1
  · rw [ite_eq_left h1]
    left
    rfl
  rw [ite_eq_right h1]
  rcases Decidable.em ((numcells == n) = true) with h2 | h2
  · rw [ite_eq_left h2]
    rcases Decidable.em (((st.eqlevFirst == level) &&
        (st.firstcode[level + 1]! == codeSentinel)) = true) with h3 | h3
    · rw [ite_eq_left h3]
      have hsent : st.firstcode[level + 1]! = codeSentinel := by
        exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp h3).2
      rcases Decidable.em (isautom ctx ((List.range n).foldl
            (fun r i => r.set! st.firstlab[i]! st.lab[i]!)
            (Array.replicate n 0)) = true) with h4 | h4
      · rw [ite_eq_left h4, ite_eq_right (by decide)]
        right
        refine ⟨_, rfl, ?_, Or.inl ⟨fun i hi => ?_, hsent, h4⟩⟩
        · rw [foldl_scatter_size, Array.size_replicate]
        · refine foldl_scatter_getElem hinj₁ (fun j hj => ?_)
            (Nat.le_refl _) hi
          rw [Array.size_replicate]
          exact hb₁ j hj
      · rw [ite_eq_right h4, ite_eq_left (by decide)]
        rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
        · rw [ite_eq_left h5]
          rcases Decidable.em (level < st.canonlevel) with h6 | h6
          · rw [ite_eq_left h6, ite_eq_right (by decide)]
            left
            rfl
          · rw [ite_eq_right h6]
            rcases Decidable.em (((testcanlab ctx (updatecan ctx
                st.canong st.canonlab st.samerows) st.lab).1 == 0) =
                true) with h7 | h7
            · rw [ite_eq_left h7]
              right
              refine ⟨_, rfl, ?_,
                Or.inr ⟨fun i hi => ?_, by simpa using h5, by omega,
                  by simpa using h7⟩⟩
              · simp only [foldl_scatter_size, Array.size_replicate]
              · refine foldl_scatter_getElem hinj₂ (fun j hj => ?_)
                  (Nat.le_refl _) hi
                simp only [foldl_scatter_size, Array.size_replicate]
                exact hb₂ j hj
            · rw [ite_eq_right h7]
              left
              rfl
        · rw [ite_eq_right h5, ite_eq_right h5]
          left
          rfl
    · rw [ite_eq_right h3, ite_eq_left (by decide)]
      rcases Decidable.em ((st.compCanon == 0) = true) with h5 | h5
      · rw [ite_eq_left h5]
        rcases Decidable.em (level < st.canonlevel) with h6 | h6
        · rw [ite_eq_left h6, ite_eq_right (by decide)]
          left
          rfl
        · rw [ite_eq_right h6]
          rcases Decidable.em (((testcanlab ctx (updatecan ctx
              st.canong st.canonlab st.samerows) st.lab).1 == 0) =
              true) with h7 | h7
          · rw [ite_eq_left h7]
            right
            refine ⟨_, rfl, ?_,
              Or.inr ⟨fun i hi => ?_, by simpa using h5, by omega,
                by simpa using h7⟩⟩
            · simp only [foldl_scatter_size, Array.size_replicate]
            · refine foldl_scatter_getElem hinj₂ (fun j hj => ?_)
                (Nat.le_refl _) hi
              simp only [Array.size_replicate]
              exact hb₂ j hj
          · rw [ite_eq_right h7]
            left
            rfl
      · rw [ite_eq_right h5, ite_eq_right h5]
        left
        rfl
  · rw [ite_eq_right h2]
    left
    rfl

/-- The successful code-one arm appends exactly the first-to-current
scatter that passed its explicit automorphism scan. -/
theorem processnode_genTrace_first {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx ((List.range n).foldl
      (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
      (Array.replicate n 0)) = true) :
    (processnode ctx level numcells st).2.genTrace =
      st.genTrace.push ((List.range n).foldl
        (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
        (Array.replicate n 0)) := by
  have hguard : (((st.eqlevFirst == level) &&
      (st.firstcode[level + 1]! == codeSentinel)) = true) := by
    simp only [Bool.and_eq_true, heq, true_and]
    exact beq_iff_eq.mpr hsent
  have hskip : ¬(st.eqlevFirst ≠ level ∧ st.compCanon < 0) := by
    intro h
    exact h.1 (beq_iff_eq.mp heq)
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace, ite_self]
  simp only [id_run_eq, forIn_range_toList, forIn_scatter_eq,
    hskip, ite_false, hnc, ite_true, hguard]
  change (if isautom ctx ((List.range n).foldl
      (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
      (Array.replicate n 0)) then
      st.genTrace.push ((List.range n).foldl
        (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
        (Array.replicate n 0))
    else _) = _
  rw [hpass]
  rfl

/-- The successful code-one event exposes the exact checked carrier it
appended, including its pointwise action from the first leaf to the current
leaf. -/
theorem processnode_firstCarrier {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hsz₁ : st.firstlab.size = n)
    (hp₁ : st.firstlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hsymm : ∀ i j, i < n → j < n →
      (ctx.g[i]!).mem j = (ctx.g[j]!).mem i)
    (hloop : ∀ i, i < n → (ctx.g[i]!).mem i = false)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx ((List.range n).foldl
      (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
      (Array.replicate n 0)) = true) :
    ∃ γ, γ ∈ (processnode ctx level numcells st).2.genTrace ∧
      checkAutom ctx.g γ = true ∧
      ∀ i, i < n → γ[st.firstlab[i]!]! = st.lab[i]! := by
  let γ := (List.range n).foldl
    (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
    (Array.replicate n 0)
  have hinj := perm_inj hsz₁ hp₁
  have hmap : ∀ i, i < n → γ[st.firstlab[i]!]! = st.lab[i]! := by
    intro i hi
    apply foldl_scatter_getElem
      (fun a b ha hb h => hinj a b (by omega) (by omega) h)
      (fun j hj => by
        rw [Array.size_replicate]
        exact perm_getElem!_lt hsz₁ hp₁ hj)
      (Nat.le_refl _) hi
  have hsize : γ.size = n := by
    simp only [γ, foldl_scatter_size, Array.size_replicate]
  have hchecked : checkAutom ctx.g γ = true :=
    checkAutom_scatter_of_isautom hsize hsz₁ hp₁ hsz₂ hp₂
      hmap hsymm hloop (by simpa only [γ] using hpass)
  refine ⟨γ, ?_, hchecked, hmap⟩
  rw [processnode_genTrace_first heq hsent hnc hpass]
  exact Array.mem_push.mpr (Or.inr rfl)

/-- The row-tied code-two arm appends exactly the incumbent-to-current
scatter, independently of which greatest-common-ancestor return it takes. -/
theorem processnode_genTrace_canon {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    (processnode ctx level numcells st).2.genTrace =
      st.genTrace.push ((List.range n).foldl
        (fun w i => w.set! st.canonlab[i]! st.lab[i]!)
        (Array.replicate n 0)) := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.genTrace),
    pushAuto_genTrace, ite_self]
  simp only [id_run_eq, forIn_range_toList, forIn_scatter_eq]
  simp [hnc, hef, hcc, hge, htie]

/-- The code-two event exposes the exact checked carrier it appended from
the incumbent leaf to the current leaf. -/
theorem processnode_canonCarrier {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n}
    (hsz₁ : st.canonlab.size = n)
    (hp₁ : st.canonlab.toList.Perm (List.range n))
    (hsz₂ : st.lab.size = n)
    (hp₂ : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx st.canonlab = leafRows ctx st.lab)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    ∃ γ, γ ∈ (processnode ctx level numcells st).2.genTrace ∧
      checkAutom ctx.g γ = true ∧
      ∀ i, i < n → γ[st.canonlab[i]!]! = st.lab[i]! := by
  let γ := (List.range n).foldl
    (fun w i => w.set! st.canonlab[i]! st.lab[i]!)
    (Array.replicate n 0)
  have hinj := perm_inj hsz₁ hp₁
  have hmap : ∀ i, i < n → γ[st.canonlab[i]!]! = st.lab[i]! := by
    intro i hi
    apply foldl_scatter_getElem
      (fun a b ha hb h => hinj a b (by omega) (by omega) h)
      (fun j hj => by
        rw [Array.size_replicate]
        exact perm_getElem!_lt hsz₁ hp₁ hj)
      (Nat.le_refl _) hi
  have hsize : γ.size = n := by
    simp only [γ, foldl_scatter_size, Array.size_replicate]
  have hchecked : checkAutom ctx.g γ = true :=
    checkAutom_scatter_of_leafRows_eq hsize hsz₁ hp₁ hsz₂ hp₂
      hmap hrows
  refine ⟨γ, ?_, hchecked, hmap⟩
  rw [processnode_genTrace_canon hef hnc hcc hge htie]
  exact Array.mem_push.mpr (Or.inr rfl)

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Permutation labellings -/

private theorem toList_eq_map_range {lab : Array Nat} {n : Nat}
    (hsz : lab.size = n) :
    ((List.range n).map fun i => lab[i]!) = lab.toList := by
  refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
  rw [List.getElem_map, List.getElem_range,
    getElem!_pos lab i (by simpa using h2)]
  simp

/-- An injective bounded labelling of full size is a permutation of
`[0, n)`: the side condition of the `checkAutom` scatter exits,
discharged from the node invariant the descents carry. -/
theorem labInj_perm_range {lab : Array Nat} {n : Nat}
    (hsz : lab.size = n) (hlab : LabOk lab n) (hinj : LabInj lab n) :
    lab.toList.Perm (List.range n) := by
  rw [List.perm_iff_count]
  intro a
  rw [← toList_eq_map_range hsz, List.count_eq_countP,
    List.count_eq_countP, List.countP_map]
  simp only [Function.comp_def]
  rcases Decidable.em (a < n) with ha | ha
  · obtain ⟨i₀, hi₀, hv⟩ := labInj_surj (by omega) hlab hinj a ha
    rw [countP_range_one (p := fun i => lab[i]! == a) hi₀
        (by simp [hv])
        (fun j hj hpj => hinj j i₀ hj hi₀ (by
          have : lab[j]! = a := by simpa using hpj
          rw [this, hv])),
      countP_range_one (p := fun i => i == a) ha (by simp)
        (fun j _ hpj => by simpa using hpj)]
  · rw [List.countP_eq_zero.mpr fun j hj hpj => by
        have hjn := List.mem_range.mp hj
        have : lab[j]! = a := by simpa using hpj
        have := hlab j (by omega)
        omega,
      List.countP_eq_zero.mpr fun j hj hpj => by
        have hjn := List.mem_range.mp hj
        have : j = a := by simpa using hpj
        omega]

/-! # Store validity, assembled per admission event -/

/-- If `processnode` records a generator, the same generator is both
checked and identified as the scatter from the first or incumbent leaf
onto the current leaf. -/
theorem processnode_carrier {level numcells : Nat} {st : SearchSt n}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 → leafRows ctx st.canonlab = leafRows ctx st.lab) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
    ∃ γ, (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ ∧ checkAutom ctx.g γ = true ∧
      ((∀ i, i < n → γ[st.firstlab[i]!]! = st.lab[i]!) ∨
       (∀ i, i < n → γ[st.canonlab[i]!]! = st.lab[i]!)) := by
  have hp₁ := labInj_perm_range hsz₁ hok₁ hinj₁
  have hpL := labInj_perm_range hszL hokL hinjL
  have hp₂ := labInj_perm_range hsz₂ hok₂ hinj₂
  have hb₁ : ∀ i, i < n → st.firstlab[i]! < n :=
    fun i hi => hok₁ i (by omega)
  have hb₂ : ∀ i, i < n → st.canonlab[i]! < n :=
    fun i hi => hok₂ i (by omega)
  rcases processnode_genTrace (level := level) (numcells := numcells)
      (fun a b ha hb he => hinj₁ a b ha hb he)
      hb₁ (fun a b ha hb he => hinj₂ a b ha hb he) hb₂ with
    h | ⟨γ, hpush, hγsz, harm⟩
  · exact Or.inl h
  · rcases harm with ⟨hsc, -, haut⟩ | ⟨hsc, -, -, htceq⟩
    · refine Or.inr ⟨γ, hpush, ?_, Or.inl hsc⟩
      exact checkAutom_scatter_of_isautom hγsz hsz₁ hp₁ hszL hpL
        hsc hsymm hloop haut
    · exact Or.inr ⟨γ, hpush,
        checkAutom_scatter_of_leafRows_eq hγsz hsz₂ hp₂ hszL hpL
          hsc (harm3 htceq), Or.inr hsc⟩

/-- Every generator `processnode` admits passes `checkAutom`, given
the run-level facts per arm: permutation facts for the three
labellings (the run invariant carries them); the code-1 arm's mandatory
`isautom` scan; and the code-2 arm's rows equality (`harm3`, discharged from the
incumbent-store account: `updatecan_inv` completes `canong` to the
incumbent's leaf rows and `testcanlab_fst` reads the tie as row
equality). -/
theorem processnode_checkAutom {level numcells : Nat} {st : SearchSt n}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 →
      leafRows ctx st.canonlab = leafRows ctx st.lab) :
    (processnode ctx level numcells st).2.genTrace = st.genTrace ∨
    ∃ γ, (processnode ctx level numcells st).2.genTrace =
        st.genTrace.push γ ∧ checkAutom ctx.g γ = true := by
  rcases processnode_carrier hsymm hloop hsz₁ hok₁ hinj₁ hszL
      hokL hinjL hsz₂ hok₂ hinj₂ harm3 with
    h | ⟨γ, hpush, hcheck, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨γ, hpush, hcheck⟩

/-! # The store-validity invariant -/

/-- Every generator the run has recorded is a checked automorphism.
This is the store-validity invariant, in the form the domination
induction threads: `processnode` is the only primitive that writes
`genTrace`, so every other event preserves it by its frame. -/
def GenTraceOk (ctx : Ctx n) (st : SearchSt n) : Prop :=
  ∀ γ ∈ st.genTrace, checkAutom ctx.g γ = true

/-- Read one checked-generator fact from the run-side store invariant. -/
theorem GenTraceOk.check {ctx : Ctx n} {st : SearchSt n}
    (h : GenTraceOk ctx st) {γ : Array Nat} (η : γ ∈ st.genTrace.toList) :
    checkAutom ctx.g γ = true :=
  h γ (Array.mem_toList_iff.mp η)

/-- The invariant survives the admission event. The only row clause is
the incumbent tie behind the `testcanlab` arm; code 1 is scanned. -/
theorem genTraceOk_processnode {level numcells : Nat} {st : SearchSt n}
    (hprev : GenTraceOk ctx st)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsz₁ : st.firstlab.size = n)
    (hok₁ : LabOk st.firstlab n) (hinj₁ : LabInj st.firstlab n)
    (hszL : st.lab.size = n)
    (hokL : LabOk st.lab n) (hinjL : LabInj st.lab n)
    (hsz₂ : st.canonlab.size = n)
    (hok₂ : LabOk st.canonlab n) (hinj₂ : LabInj st.canonlab n)
    (harm3 : (testcanlab ctx
        (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 =
        0 →
      leafRows ctx st.canonlab = leafRows ctx st.lab) :
    GenTraceOk ctx (processnode ctx level numcells st).2 := by
  intro γ hγ
  rcases processnode_checkAutom hsymm hloop hsz₁ hok₁ hinj₁ hszL
      hokL hinjL hsz₂ hok₂ hinj₂ harm3 with heq | ⟨δ, hpush, hδ⟩
  · rw [heq] at hγ
    exact hprev γ hγ
  · rw [hpush] at hγ
    rcases Array.mem_push.mp hγ with hmem | rfl
    · exact hprev γ hmem
    · exact hδ

end Hex.GraphIso.Nauty
