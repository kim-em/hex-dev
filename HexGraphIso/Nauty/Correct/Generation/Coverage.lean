/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Reference
public import HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Nauty.Correct.Generation.Reference
import all HexGraphIso.Nauty.Invariant.Orbits

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- A specific leaf key occurs below a refined state, following the
specification's target cells. Both the key and the target-position sequence
are retained, so the occurrence can justify the executable reference hints
independently of whether the key is the maximum of the subtree. -/
def HasLeaf (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (targets : List Nat) (key : Key n) : Prop :=
  ∃ path leafLevel leaf,
    DescPath ctx level st path leafLevel leaf ∧ referenceTargets ctx tcLevel level st path ∧
      (∀ q, q < n → leaf.ptn[q]! ≤ leafLevel) ∧
      targets = path.map Prod.fst ∧ key = ⟨referenceCodes ctx level st path ++ [codeSentinel], leafRows ctx leaf.lab⟩

/-- A discrete state supplies its own leaf. -/
theorem HasLeaf.leaf {tcLevel level : Nat} {st : RefineSt n}
    (hdisc : ∀ q, q < n → st.ptn[q]! ≤ level) :
    HasLeaf ctx tcLevel level st [] ⟨[st.longcode, codeSentinel], leafRows ctx st.lab⟩ :=
  ⟨[], level, st, .refl _ _, trivial, hdisc, rfl, rfl⟩

/-- A child occurrence supplies the corresponding parent occurrence. -/
theorem HasLeaf.step {tcLevel level tc e o : Nat} {st : RefineSt n} {targets : List Nat} {key : Key n}
    (hlvl : level < n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc)
    (htarget : tc = specTargetcell ctx st.lab st.ptn level tcLevel)
    (h : HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) targets key) :
    HasLeaf ctx tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.rows⟩ := by
  obtain ⟨path, leafLevel, leaf, hdesc, htargets, hdisc, rfl, rfl⟩ := h
  exact ⟨(tc, o) :: path, leafLevel, leaf,
    .step tc e o hlvl hcell hne ho hdesc, ⟨htarget, htargets⟩, hdisc, rfl, rfl⟩

/-- An occurring key comes from this discrete state or from one child
of the specified target cell. -/
theorem HasLeaf.cases {tcLevel level : Nat} {st : RefineSt n} {targets : List Nat} {key : Key n}
    (h : HasLeaf ctx tcLevel level st targets key) :
    ((∀ q, q < n → st.ptn[q]! ≤ level) ∧ targets = [] ∧
      key = ⟨[st.longcode, codeSentinel], leafRows ctx st.lab⟩) ∨
    ∃ tc e o rest tail, level < n ∧ (tc, e) ∈ cells st.ptn level n ∧
      tc < e ∧ o ≤ e - tc ∧ tc = specTargetcell ctx st.lab st.ptn level tcLevel ∧
      HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + o]!) rest tail ∧
      targets = tc :: rest ∧
      key = ⟨st.longcode :: tail.codes, tail.rows⟩ := by
  obtain ⟨path, leafLevel, leaf, hdesc, htargets, hdisc, htcs, hkey⟩ := h
  cases hdesc with
  | refl => exact Or.inl ⟨hdisc, htcs, hkey⟩
  | step tc e o hlvl hcell hne ho htail =>
    rename_i path
    let tail : Key n := ⟨referenceCodes ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) path ++ [codeSentinel], leafRows ctx leaf.lab⟩
    refine Or.inr ⟨tc, e, o, path.map Prod.fst, tail, hlvl, hcell, hne, ho, htargets.1, ?_, htcs, hkey⟩
    exact ⟨_, _, _, htail, htargets.2, hdisc, rfl, rfl⟩

/-- Leaf occurrence transports through a row-preserving renaming and
cell equivalence. In particular, this applies to implicit pruning
carriers without requiring them to be recorded generators. -/
theorem HasLeaf.transport {σ : Renaming n} (hg : RowsMap σ ctx.g ctx.g)
    {tcLevel level : Nat} {U V : RefineSt n} {targets : List Nat} {key : Key n}
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (h : HasLeaf ctx tcLevel level U targets key) : HasLeaf ctx tcLevel level V targets key := by
  obtain ⟨path, leafLevel, leaf, hdesc, htargets, hdisc, rfl, rfl⟩ := h
  obtain ⟨leaf', path', hdesc', htargets', htcs, hcodes, hlab, hptn⟩ :=
    reference_leaf hg hdesc htargets hU hsp hdisc
  have hleaf := descends_iterOk hdesc.descends hU
  refine ⟨path', leafLevel, leaf', hdesc', htargets', ?_, htcs.symm, ?_⟩
  · simpa only [hptn] using hdisc
  · rw [hcodes, hlab, leafRows_map σ hg hleaf.ok.labOk hleaf.ok.labSize]

/-- A checked carrier between two children preserves occurrence of every
specific leaf key, not only equality of the maximal child keys. -/
theorem HasLeaf.carried {tcLevel level tc e oU oV : Nat}
    {st : RefineSt n} {γ : Array Nat} {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g γ = true)
    (hstab : CellStab st.ptn level st.lab γ)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hmap : γ[st.lab[tc + oU]!]! = st.lab[tc + oV]!)
    (h : HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    HasLeaf ctx tcLevel (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hgsz hcheck
  have he : st.lab.map σ.toFun = st.lab.map (fun v => γ[v]!) :=
    map_congr_of_labOk hok.ok.labOk fun v hv => hσ v hv
  have hsp : StPerm level st (mapSt σ st) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp, ?_⟩
    change cellsPerm st.ptn level st.lab (st.lab.map σ.toFun)
    rw [he]
    exact hstab
  have heBound := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  have hv : st.lab[tc + oU]! < n := hok.ok.labOk _ (by rw [hok.ok.labSize]; omega)
  have hmap' : st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! :=
    hmap.symm.trans (hσ _ hv).symm
  exact h.transport hrows (iterOk_child hok hlvl hcell hne hoU)
    (stPerm_child hrows hsp hok hcell hne hoV hoU hmap')

/-- A checked automorphism identifies the sets of leaf keys below the
two children it relates. The reverse carrier is a forward word in the
same permutation, using finite permutation cycles. -/
theorem HasLeaf.carried_iff {tcLevel level tc e oU oV : Nat}
    {st : RefineSt n} {γ : Array Nat} {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g γ = true)
    (hstab : CellStab st.ptn level st.lab γ)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hmap : γ[st.lab[tc + oU]!]! = st.lab[tc + oV]!) :
    HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + oU]!) targets key ↔
      HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  constructor
  · exact HasLeaf.carried hok hlvl hgsz hcheck hstab hcell hne hoU hoV hmap
  · intro h
    have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
    have hu := hok.ok.labOk (tc + oU) (by rw [hok.ok.labSize]; omega)
    have hv := hok.ok.labOk (tc + oV) (by rw [hok.ok.labSize]; omega)
    have hchecks : ∀ δ ∈ [γ], checkAutom ctx.g δ = true := by
      intro δ hδ
      rwa [List.mem_singleton.mp hδ]
    have hstabs : ∀ δ ∈ [γ], CellStab st.ptn level st.lab δ := by
      intro δ hδ
      rwa [List.mem_singleton.mp hδ]
    obtain ⟨w, hw, hact⟩ := wordConn_symm
      (fun δ hδ => checkAutom_bound (hchecks δ hδ))
      (fun δ hδ => checkAutom_inj (hchecks δ hδ)) [γ] hu
      (fun _ hδ => hδ) (by simpa only [applyWord, List.foldl_cons, List.foldl_nil] using hmap)
    obtain ⟨hca, hst, hval⟩ := wordPerm_spec hok.ok.labOk hok.ok.ptnSize hok.ok.labSize
      hok.ok.ptnEnd hchecks hstabs w hw
    exact h.carried hok hlvl hgsz hca hst hcell hne hoV hoU
      ((hval _ hv).trans hact)

/-- The first code of every occurring leaf is the current refinement
code, even when another leaf has a larger key. -/
theorem HasLeaf.head {tcLevel level : Nat} {st : RefineSt n} {targets : List Nat} {key : Key n}
    (h : HasLeaf ctx tcLevel level st targets key) : ∃ tail, key.codes = st.longcode :: tail := by
  obtain ⟨path, _, _, _, _, _, _, rfl⟩ := h
  cases path with
  | nil => exact ⟨[codeSentinel], rfl⟩
  | cons step path => exact ⟨_, rfl⟩

/-- A discrete node cannot hide a deeper matching leaf. -/
theorem HasLeaf.discrete {tcLevel level : Nat} {st : RefineSt n} {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hdisc : ∀ q, q < n → st.ptn[q]! ≤ level)
    (h : HasLeaf ctx tcLevel level st targets key) :
    targets = [] ∧ key = ⟨[st.longcode, codeSentinel], leafRows ctx st.lab⟩ := by
  obtain ⟨path, leafLevel, leaf, hdesc, _, _, htcs, hkey⟩ := h
  cases hdesc with
  | refl => exact ⟨htcs, hkey⟩
  | step tc e o _ hcell hne _ _ =>
    have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
    have hopen := target_open hok.ok.ptnSize hok.ok.ptnEnd hcell tc (Nat.le_refl _) hne
    have hclosed := hdisc tc (by omega)
    omega

end Hex.GraphIso.Nauty.Generation
