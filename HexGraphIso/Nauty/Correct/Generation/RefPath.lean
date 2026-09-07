/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Transport

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

end Hex.GraphIso.Nauty.Generation
