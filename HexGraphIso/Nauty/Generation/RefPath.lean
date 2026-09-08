/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Transport
import all HexGraphIso.Nauty.Invariant.Orbits
import all HexGraphIso.Generated
public import HexGraphIso.Orbit
public import HexGraphIso.Nauty.Generation.Stabilizer

import all HexGraphIso.Orbit

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- A reference occurrence retaining uniformity at and below a saved
boundary. The target hints and complete leaf key remain part of the
witness when pruning transports it to another child. -/
inductive RefPath (ctx : Ctx n) (tcLevel boundary : Nat) :
    Nat → RefineSt n → List Nat → Key n → Prop where
  | leaf {level : Nat} {rs : RefineSt n}
      (discrete : ∀ q, q < n → rs.ptn[q]! ≤ level) :
      RefPath ctx tcLevel boundary level rs [] ⟨[rs.longcode, codeSentinel], leafRows ctx rs.lab⟩
  | step {level tc e o : Nat} {rs : RefineSt n} {targets : List Nat} {key : Key n}
      (depth : level < n) (cell : (tc, e) ∈ cells rs.ptn level n)
      (nontrivial : tc < e) (offset : o ≤ e - tc)
      (target : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel)
      (child : RefPath ctx tcLevel boundary (level + 1)
        (childSt ctx level rs tc rs.lab[tc + o]!) targets key)
      (uniform : boundary ≤ level →
        Uniform ctx tcLevel level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩) :
      RefPath ctx tcLevel boundary level rs (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩

/-- Forgetting uniformity gives the ordinary reference occurrence. -/
theorem RefPath.occurs {tcLevel boundary level : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n} (h : RefPath ctx tcLevel boundary level rs targets key) :
    HasLeaf ctx tcLevel level rs targets key := by
  induction h with
  | leaf hd => exact HasLeaf.leaf hd
  | step hl hc hn ho ht _ _ ih => exact ih.step hl hc hn ho ht

/-- At the saved boundary, the richer occurrence supplies the uniform
subtree premise needed by the emission theorem. -/
theorem RefPath.uniform {tcLevel boundary level : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n} (h : RefPath ctx tcLevel boundary level rs targets key)
    (hok : IterOk ctx level rs) (hb : boundary ≤ level) :
    Uniform ctx tcLevel level rs targets key := by
  cases h with
  | leaf hd => exact Uniform.leaf hok hd
  | step _ _ _ _ _ _ hu => exact hu hb

/-- Moving a saved boundary deeper weakens the uniformity obligation. -/
theorem RefPath.raise {tcLevel boundary boundary' level : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n} (h : RefPath ctx tcLevel boundary level rs targets key)
    (hb : boundary ≤ boundary') : RefPath ctx tcLevel boundary' level rs targets key := by
  induction h with
  | leaf hd => exact .leaf hd
  | step hl hc hn ho ht _ hu ih =>
    exact .step hl hc hn ho ht ih (fun hlevel => hu (Nat.le_trans hb hlevel))

/-- In a uniform subtree, every reference occurrence carries uniformity
at every later boundary along its path. -/
theorem HasLeaf.uniformPath {tcLevel boundary level : Nat} {rs : RefineSt n}
    {targets : List Nat} {key : Key n} (h : HasLeaf ctx tcLevel level rs targets key)
    (hok : IterOk ctx level rs) (hu : Uniform ctx tcLevel level rs targets key) :
    RefPath ctx tcLevel boundary level rs targets key := by
  rcases h.cases with ⟨hd, rfl, rfl⟩ |
    ⟨tc, e, o, rest, tail, hl, hc, hn, ho, ht, hchild, rfl, rfl⟩
  · exact .leaf hd
  · exact .step hl hc hn ho ht
      (hchild.uniformPath (iterOk_child hok hl hc hn ho) (hu.child hl hc hn ht ho))
      (fun _ => hu)
termination_by targets.length

/-- Graph and cell isomorphisms transport the reference and all its
saved uniformity premises, including through unrecorded checked carriers. -/
theorem RefPath.transport {σ τ : Renaming n} {tcLevel boundary level : Nat}
    {U V : RefineSt n} {targets : List Nat} {key : Key n}
    (h : RefPath ctx tcLevel boundary level U targets key)
    (hg : RowsMap σ ctx.g ctx.g) (hback : RowsMap τ ctx.g ctx.g)
    (hinv : ∀ v, v < n → τ (σ v) = v)
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U)) :
    RefPath ctx tcLevel boundary level V targets key := by
  induction h generalizing V with
  | @leaf level U hdisc =>
    have hV := iterOk_of_stPerm hU hsp
    have hptn : U.ptn = V.ptn := hsp.ptn
    have hVdisc : ∀ q, q < n → V.ptn[q]! ≤ level := by
      intro q hq
      rw [← hptn]
      exact hdisc q hq
    have hlab : V.lab = U.lab.map σ.toFun :=
      (stPerm_lab_eq hsp (by rw [hV.ok.ptnSize]; exact hVdisc)
        (by rw [hV.ok.labSize, hV.ok.ptnSize])).symm
    have hcode : U.longcode = V.longcode := hsp.longcode
    have hrows : leafRows ctx U.lab = leafRows ctx V.lab := by
      rw [hlab, leafRows_map σ hg hU.ok.labOk hU.ok.labSize]
    rw [hcode, hrows]
    exact .leaf hVdisc
  | @step level tc e o U targets key hlvl hcell hne ho htarget htail hu ih =>
    have hV := iterOk_of_stPerm hU hsp
    have hptn : U.ptn = V.ptn := hsp.ptn
    have hcellV : (tc, e) ∈ cells V.ptn level n := by rw [← hptn]; exact hcell
    have hen : e < n := target_end_lt hV.ok.ptnSize hV.ok.ptnEnd hcellV
    have hcellIsV : IsCell V.ptn level tc (e + 1 - tc) :=
      cells_isCell (by rw [hV.ok.ptnSize]; exact Nat.le_refl _) hV.ok.ptnEnd _ hcellV
    have hmemU : σ.toFun U.lab[tc + o]! ∈ segN (U.lab.map σ.toFun) tc (e + 1 - tc) := by
      rw [segN_map (by rw [hU.ok.labSize]; omega)]
      exact List.mem_map.mpr
        ⟨U.lab[tc + o]!, mem_segN_iff.mpr ⟨o, by omega, rfl⟩, rfl⟩
    have hmemV := (hsp.cells tc (e + 1 - tc) hcellIsV).mem_iff.mpr hmemU
    obtain ⟨oV, hoVlt, hoVval⟩ := mem_segN_iff.mp hmemV
    have hsp' := stPerm_child hg hsp hU hcell hne (by omega) ho hoVval
    have htailV := ih (iterOk_child hU hlvl hcell hne ho) hsp'
    have hcode : U.longcode = V.longcode := hsp.longcode
    rw [hcode]
    refine .step hlvl hcellV hne (by omega) (htarget.trans (reference_target hg hU hsp).symm) htailV ?_
    intro hb
    have h := (hu hb).transport hU hsp hback hinv
    rwa [hcode] at h

/-- A checked cell stabilizer moves a richer reference occurrence to
another child without losing its saved uniformity boundary. Membership
in the emitted generator group is not required. -/
theorem RefPath.carried {tcLevel boundary level tc e oU oV : Nat}
    {st : RefineSt n} {γ : Array Nat} {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g γ = true)
    (hstab : CellStab st.ptn level st.lab γ)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hmap : γ[st.lab[tc + oU]!]! = st.lab[tc + oV]!)
    (h : RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) targets key) :
    RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  obtain ⟨σ, hσ, hrows⟩ := checkAutom_sound hgsz hcheck
  obtain ⟨τ, hτ, hback⟩ := checkAutom_sound hgsz (checkAutom_invPerm hcheck)
  have hs : γ.size = n := by
    have hc := hcheck
    rw [checkAutom] at hc
    simp only [Bool.and_eq_true] at hc
    exact beq_iff_eq.mp hc.1.1.1
  have hinv : ∀ v, v < n → τ (σ v) = v := by
    intro v hv
    rw [hτ _ ((σ.maps v).mp hv), hσ v hv]
    exact getElem!_invPerm γ
      (fun a b ha hb => checkAutom_inj hcheck a b (by omega) (by omega))
      (by omega) (by rw [hs]; exact checkAutom_bound hcheck v hv)
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
  exact h.transport hrows hback hinv (iterOk_child hok hlvl hcell hne hoU)
    (stPerm_child hrows hsp hok hcell hne hoV hoU hmap')

/-- A checked automorphism identifies the sets of leaf keys below the
two children it relates. The reverse carrier is a forward word in the
same permutation, using finite permutation cycles. -/
theorem RefPath.carried_iff {tcLevel boundary level tc e oU oV : Nat}
    {st : RefineSt n} {γ : Array Nat} {targets : List Nat} {key : Key n}
    (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g γ = true)
    (hstab : CellStab st.ptn level st.lab γ)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hmap : γ[st.lab[tc + oU]!]! = st.lab[tc + oV]!) :
    RefPath ctx tcLevel boundary (level + 1) (childSt ctx level st tc st.lab[tc + oU]!) targets key ↔
      RefPath ctx tcLevel boundary (level + 1) (childSt ctx level st tc st.lab[tc + oV]!) targets key := by
  constructor
  · exact RefPath.carried hok hlvl hgsz hcheck hstab hcell hne hoU hoV hmap
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


/-- Every image of a reference child under the true path stabilizer
contains the same reference occurrence. This supplies the matching-search
premise before any generation theorem has been established. -/
theorem RefPath.orbit {k : Nat} {G : Colored n k} {base : List (Fin n)} {rs : RefineSt n} {st : SearchSt n}
    {tcLevel boundary level tc e oU oV : Nat} {u v : Fin n} {targets : List Nat} {key : Key n}
    (hok : IterOk { g := rowsOf G } level rs) (hlvl : level < n)
    (hpath : PathStab { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2) (initialPartition G).1 level st)
    (hlab : st.lab = rs.lab) (hptn : st.ptn = rs.ptn)
    (hbase : ∀ b : Fin n, st.fixedpts.mem b.val = true → b ∈ base)
    (hcell : (tc, e) ∈ cells rs.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hatU : rs.lab[tc + oU]! = u.val) (hatV : rs.lab[tc + oV]! = v.val)
    (horbit : Aut.Orbit G base u v)
    (h : RefPath { g := rowsOf G } tcLevel boundary (level + 1)
      (childSt { g := rowsOf G } level rs tc rs.lab[tc + oU]!) targets key) :
    RefPath { g := rowsOf G } tcLevel boundary (level + 1)
      (childSt { g := rowsOf G } level rs tc rs.lab[tc + oV]!) targets key := by
  obtain ⟨p, hp, hfix, hmap⟩ := horbit
  have hstab := path_stab (by omega : 0 < n) hpath hp (fun b hb => hfix b (hbase b hb))
  rw [hlab, hptn] at hstab
  apply h.carried hok hlvl (size_rowsOf G)
    (checkAutom_renaming (ctx := { g := rowsOf G }) (renamingOf p) (rowsMap_of_isIso hp))
    hstab hcell hne hoU hoV
  rw [hatU, hatV, renamingArray_get _ u.isLt, renamingOf_lt p u.isLt, hmap]

end Hex.GraphIso.Nauty.Generation
