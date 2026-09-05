/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.NodePacked
public import HexGraphIso.Separator

public section

/-!
The separator routes over packed kernel state: the root refinement
code (`sepRootP`) and the root node's two codes (`nodeSepP`),
replayed with the packed refinement of `HexGraphIso.NodePacked` and
proven equal to the list clones of `HexGraphIso.Separator`, which the
packed-set originals are proven equal to there. The tactic's root and
two-code separator obligations replay these on the rows tied as one
packed number.
-/

namespace Hex.GraphIso

open Nauty

variable {n k : Nat}

/-- The root refinement code over packed state, for `2 ≤ n`. -/
@[expose] def sepRootP (n rows : Nat) (lab0 ptn0 : Nat) (cellEnds : List Nat) : Nat :=
  (refineP (initCtx n rows) 1 lab0 ptn0 (initActive n cellEnds).toNat
    cellEnds.length).longcode

theorem sepRootP_eq (G : Colored n k) (flat : List Bool) (hn : 2 ≤ n) :
    some (sepRootP n (packRowsK n flat) (initLabP G) (initPtnP G)
        (initialPartition G).2) =
      sepRootL n (flatRows n flat).toList (initialPartition G).1.toList
        (initialPartition G).2 := by
  rw [sepRootL, sepRootP, packRowsK_eq]
  obtain ⟨hctx, hlab, hptn⟩ := initRep G flat (by omega)
  have hrs := refineP_eq hctx (level := 1)
    (by show (1 : Nat) < 2 ^ initW n; have := initW_lt n; omega) hlab hptn
    (initActive n (initialPartition G).2).toNat (initialPartition G).2.length
  rw [hrs.longcode]

/-- `nodeSep` over packed state. -/
@[expose] def nodeSepP (ctx : CtxP) (level lab ptn active numcells : Nat) :
    Option Nat × Option Nat :=
  let rs := refineP ctx level lab ptn active numcells
  cond (discreteAtP ctx rs.ptn level) (some rs.longcode, some codeSentinel)
    (let tcr := specMaketargetcellP ctx rs.lab rs.ptn level 100
    let childHead := fun (o : Nat) =>
      let br := breakoutP ctx rs.lab rs.ptn (Nat.add level 1) tcr.1
        (lget ctx rs.lab (Nat.add tcr.1 o))
      (refineP ctx (Nat.add level 1) br.1 br.2.1 br.2.2 (Nat.add rs.numcells 1)).longcode
    (some rs.longcode,
      some ((List.range (Nat.sub tcr.2.2 1)).foldl
        (fun mx j => maxK mx (childHead (Nat.add j 1))) (childHead 0))))

theorem nodeSepP_eq {ctx : CtxP} {ctxL : CtxL} (h : CtxRep ctx ctxL)
    {level : Nat} (hlev : level + 1 < 2 ^ ctx.w) {labP : Nat} {lab : List Nat}
    (hl : Rep ctx.w ctx.n labP lab) {ptnP : Nat} {ptn : List Nat}
    (hp : Rep ctx.w ctx.n ptnP ptn) (active numcells : Nat) :
    nodeSepP ctx level labP ptnP active numcells =
      nodeSepL ctxL level lab ptn active numcells := by
  have hrs := refineP_eq h (level := level) (by omega) hl hp active numcells
  have hdisc : discreteAtP ctx (refineP ctx level labP ptnP active numcells).ptn level =
      discreteAtL (refineL ctxL level lab ptn active numcells).ptn level ctxL.n :=
    discreteAtP_eq h hrs.ptn level
  have htc : specMaketargetcellP ctx (refineP ctx level labP ptnP active numcells).lab
      (refineP ctx level labP ptnP active numcells).ptn level 100 =
      specMaketargetcellL ctxL (refineL ctxL level lab ptn active numcells).lab
        (refineL ctxL level lab ptn active numcells).ptn level 100 :=
    specMaketargetcellP_eq h hrs.lab hrs.ptn level 100
  have hchild : ∀ (tc o : Nat),
      (refineP ctx (level + 1)
        (breakoutP ctx (refineP ctx level labP ptnP active numcells).lab
          (refineP ctx level labP ptnP active numcells).ptn (level + 1) tc
          (lget ctx (refineP ctx level labP ptnP active numcells).lab (tc + o))).1
        (breakoutP ctx (refineP ctx level labP ptnP active numcells).lab
          (refineP ctx level labP ptnP active numcells).ptn (level + 1) tc
          (lget ctx (refineP ctx level labP ptnP active numcells).lab (tc + o))).2.1
        (breakoutP ctx (refineP ctx level labP ptnP active numcells).lab
          (refineP ctx level labP ptnP active numcells).ptn (level + 1) tc
          (lget ctx (refineP ctx level labP ptnP active numcells).lab (tc + o))).2.2
        ((refineL ctxL level lab ptn active numcells).numcells + 1)).longcode =
      (refineL ctxL (level + 1)
        (breakoutL ctxL.n (refineL ctxL level lab ptn active numcells).lab
          (refineL ctxL level lab ptn active numcells).ptn (level + 1) tc
          (atD (refineL ctxL level lab ptn active numcells).lab (tc + o) 0)).1
        (breakoutL ctxL.n (refineL ctxL level lab ptn active numcells).lab
          (refineL ctxL level lab ptn active numcells).ptn (level + 1) tc
          (atD (refineL ctxL level lab ptn active numcells).lab (tc + o) 0)).2.1
        (breakoutL ctxL.n (refineL ctxL level lab ptn active numcells).lab
          (refineL ctxL level lab ptn active numcells).ptn (level + 1) tc
          (atD (refineL ctxL level lab ptn active numcells).lab (tc + o) 0)).2.2
        ((refineL ctxL level lab ptn active numcells).numcells + 1)).longcode := by
    intro tc o
    have hbr := breakoutP_eq h hrs.lab hrs.ptn hlev tc
      (lget_lt h (refineP ctx level labP ptnP active numcells).lab (tc + o))
    rw [lget_eq h hrs.lab] at hbr ⊢
    obtain ⟨hbr1, hbr2, hbr3⟩ := hbr
    rw [hbr3]
    exact (refineP_eq h (level := level + 1) hlev hbr1 hbr2 _ _).longcode
  rw [nodeSepP, nodeSepL]
  dsimp only
  simp only [hdisc, htc, hrs.longcode, hchild, hrs.numcells, cond_beq_true, add_eq, sub_eq,
    maxK_eq]

/-- `sepCodes` over packed state, for `2 ≤ n`. -/
@[expose] def sepCodesP (n rows lab0 ptn0 : Nat) (cellEnds : List Nat) :
    Option Nat × Option Nat :=
  nodeSepP (initCtx n rows) 1 lab0 ptn0 (initActive n cellEnds).toNat cellEnds.length

theorem sepCodesP_eq (G : Colored n k) (flat : List Bool) (hn : 2 ≤ n) :
    sepCodesP n (packRowsK n flat) (initLabP G) (initPtnP G) (initialPartition G).2 =
      sepCodesL n (flatRows n flat).toList (initialPartition G).1.toList
        (initialPartition G).2 := by
  rw [sepCodesL, sepCodesP, packRowsK_eq]
  obtain ⟨hctx, hlab, hptn⟩ := initRep G flat (by omega)
  exact nodeSepP_eq hctx (by have := initW_lt n; show 1 + 1 < 2 ^ initW n; omega)
    hlab hptn _ _

/-- The two-code separator on the tied packed rows. -/
@[expose] def sepDiffLitP (G H : Colored n k) (NA NB : Nat) : Bool :=
  decide (2 ≤ n) &&
  sepPair (sepCodesP n NA (initLabP G) (initPtnP G) (initialPartition G).2)
    (sepCodesP n NB (initLabP H) (initPtnP H) (initialPartition H).2)

theorem not_isomorphic_of_sepDiffLitP {G H : Colored n k} {NA NB : Nat}
    (hA : packRowsK n G.graph.adjMatrix.data.toList = NA)
    (hB : packRowsK n H.graph.adjMatrix.data.toList = NB)
    (h : sepDiffLitP G H NA NB = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [sepDiffLitP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, h⟩ := h
  rw [sepCodesP_eq G _ hn, sepCodesP_eq H _ hn] at h
  refine not_isomorphic_of_sepDiffLit rfl rfl ?_
  rw [sepDiffLit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hn, h⟩

/-- The root separator on the tied packed rows. -/
@[expose] def sepRootLitP (G H : Colored n k) (NA NB : Nat) : Bool :=
  decide (2 ≤ n) &&
  !Nat.beq (sepRootP n NA (initLabP G) (initPtnP G) (initialPartition G).2)
    (sepRootP n NB (initLabP H) (initPtnP H) (initialPartition H).2)

theorem not_isomorphic_of_sepRootLitP {G H : Colored n k} {NA NB : Nat}
    (hA : packRowsK n G.graph.adjMatrix.data.toList = NA)
    (hB : packRowsK n H.graph.adjMatrix.data.toList = NB)
    (h : sepRootLitP G H NA NB = true) : ¬Isomorphic G H := by
  subst hA hB
  rw [sepRootLitP, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, h⟩ := h
  refine not_isomorphic_of_sepRootLit rfl rfl ?_
  rw [sepRootLit, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hn, ?_⟩
  rw [← sepRootP_eq G _ hn, ← sepRootP_eq H _ hn]
  rw [Bool.not_eq_true', beq_eq_beq, beq_eq_false_iff_ne] at h
  rw [optNe]
  simpa using h

end Hex.GraphIso
