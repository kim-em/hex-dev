/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

/-- Refinement codes along an individualization path, including the code
at its final refined state. This is proof-side reference data. -/
def referenceCodes (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    List (Nat × Nat) → List Nat
  | [] => [st.longcode]
  | (tc, o) :: path => st.longcode :: referenceCodes ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) path

/-- Every step uses the specification's target-cell rule. -/
def referenceTargets (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n) :
    List (Nat × Nat) → Prop
  | [] => True
  | (tc, o) :: path => tc = specTargetcell ctx st.lab st.ptn level tcLevel ∧
      referenceTargets ctx tcLevel (level + 1)
        (childSt ctx level st tc st.lab[tc + o]!) path

/-- Isomorphic cell-equivalent states choose the same target position. -/
theorem reference_target {σ : Renaming n} (hg : RowsMap σ ctx.g ctx.g)
    {level tcLevel : Nat} {U V : RefineSt n}
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U)) :
    specTargetcell ctx V.lab V.ptn level tcLevel =
      specTargetcell ctx U.lab U.ptn level tcLevel := by
  have hV := iterOk_of_stPerm hU hsp
  have he := specTargetcell_perm (ctx := ctx) (tcLevel := tcLevel) hsp.cells
    (by rw [hV.ok.ptnSize]; exact Nat.le_refl _) hV.ok.ptnEnd
  have hptn : U.ptn = V.ptn := hsp.ptn
  change specTargetcell ctx V.lab V.ptn level tcLevel =
    specTargetcell ctx (U.lab.map σ.toFun) V.ptn level tcLevel at he
  rw [← hptn, specTargetcell_map σ hg hU.ok.labOk hU.ok.labSize hU.ok.ptnSize hU.ok.ptnEnd] at he
  simpa only [hptn] using he

/-- Transporting a reference descent preserves both the target cells and
every refinement code. Unlike equality of maximal keys, this retains the
specific reference path needed by the first-reference comparison. -/
theorem reference_transport {tcLevel : Nat} {σ : Renaming n}
    (hg : RowsMap σ ctx.g ctx.g) :
    ∀ {level level' : Nat} {p : List (Nat × Nat)} {U U' V : RefineSt n},
      DescPath ctx level U p level' U' → referenceTargets ctx tcLevel level U p →
      IterOk ctx level U →
      StPerm level V (mapSt σ U) →
      ∃ V' q, DescPath ctx level V q level' V' ∧
        referenceTargets ctx tcLevel level V q ∧ q.map Prod.fst = p.map Prod.fst ∧
        referenceCodes ctx level V q = referenceCodes ctx level U p ∧
        StPerm level' V' (mapSt σ U')
  | _, _, _, _, _, V, .refl _ _, _, _, hsp =>
    ⟨V, [], .refl _ _, trivial, rfl,
      by simp only [referenceCodes]; exact congrArg (fun c => [c]) hsp.longcode.symm, hsp⟩
  | level, level', _, U, U', V,
      .step tc e o hlvl hcell hne ho htail, htargets, hU, hsp => by
    have hV := iterOk_of_stPerm hU hsp
    have hptn : U.ptn = V.ptn := hsp.ptn
    have hpszV := hV.ok.ptnSize
    have hendV := hV.ok.ptnEnd
    have hcellV : (tc, e) ∈ cells V.ptn level n := by
      rw [← hptn]
      exact hcell
    have hen : e < n := target_end_lt hpszV hendV hcellV
    have hcellIsV : IsCell V.ptn level tc (e + 1 - tc) :=
      cells_isCell (by omega) hendV _ hcellV
    have hmemU : σ.toFun U.lab[tc + o]! ∈
        segN (U.lab.map σ.toFun) tc (e + 1 - tc) := by
      rw [segN_map (by rw [hU.ok.labSize]; omega)]
      exact List.mem_map.mpr
        ⟨U.lab[tc + o]!, mem_segN_iff.mpr ⟨o, by omega, rfl⟩, rfl⟩
    have hcpT := hsp.cells tc (e + 1 - tc) hcellIsV
    have hmemV : σ.toFun U.lab[tc + o]! ∈
        segN V.lab tc (e + 1 - tc) := hcpT.mem_iff.mpr hmemU
    obtain ⟨oV, hoVlt, hoVval⟩ := mem_segN_iff.mp hmemV
    have hsp' := stPerm_child hg hsp hU hcell hne
      (by omega) ho hoVval
    have hUok' := iterOk_child hU hlvl hcell hne ho
    obtain ⟨V', q, hdesc, htargetsV, hq, hcodes, hspL⟩ :=
      reference_transport hg htail htargets.2 hUok' hsp'
    refine ⟨V', (tc, oV) :: q,
      .step tc e oV hlvl hcellV hne (by omega) hdesc,
      ⟨htargets.1.trans (reference_target hg hU hsp).symm, htargetsV⟩,
      by rw [List.map_cons, List.map_cons, hq], ?_, hspL⟩
    simp only [referenceCodes, hcodes]
    rw [show V.longcode = U.longcode from hsp.longcode.symm]


/-- At a discrete reference leaf, transport gives the exact renamed
labelling, as well as every refinement code and target-cell position.
Keeping the labelling is essential for identifying the automorphism. -/
theorem reference_leaf {tcLevel : Nat} {σ : Renaming n} (hg : RowsMap σ ctx.g ctx.g)
    {level level' : Nat} {path : List (Nat × Nat)} {U U' V : RefineSt n}
    (h : DescPath ctx level U path level' U')
    (htargets : referenceTargets ctx tcLevel level U path)
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V' q, DescPath ctx level V q level' V' ∧
      referenceTargets ctx tcLevel level V q ∧ q.map Prod.fst = path.map Prod.fst ∧
      referenceCodes ctx level V q = referenceCodes ctx level U path ∧
      V'.lab = U'.lab.map σ.toFun ∧ V'.ptn = U'.ptn := by
  obtain ⟨V', q, hdesc, htargetsV, hq, hcodes, hspL⟩ := reference_transport hg h htargets hU hsp
  have hU' := descends_iterOk h.descends hU
  have hV' := iterOk_of_stPerm hU' hspL
  have hptn : U'.ptn = V'.ptn := hspL.ptn
  have hVdisc : ∀ z, z < V'.ptn.size → V'.ptn[z]! ≤ level' := by
    intro z hz
    rw [← hptn]
    rw [hV'.ok.ptnSize] at hz
    exact hdisc z hz
  have hVsz : V'.lab.size = V'.ptn.size := by
    rw [hV'.ok.labSize, hV'.ok.ptnSize]
  exact ⟨V', q, hdesc, htargetsV, hq, hcodes, (stPerm_lab_eq hspL hVdisc hVsz).symm, hptn.symm⟩

end Hex.GraphIso.Nauty.Generation
