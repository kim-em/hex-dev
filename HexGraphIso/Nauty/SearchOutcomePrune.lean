/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeFinal
import all HexGraphIso.Nauty.Search

public section

/-! Comparison-prune producers for the corrected search outcomes. -/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

namespace RunPrep

/-- A negative comparison branch whose prune tail stays below the recorded
divergence produces a frozen-code witness without changing the incumbent. -/
theorem frozen {G : Colored n k} {ctx : Ctx}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n)
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0)
    (hfloor : Int.ofNat st.eqlevCanon.toNat ≤
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
      (processnode ctx current numcells st).1 := by
  subst n
  have hcc : st.compCanon = -1 := by
    rcases h.codeInv.tri with hzero |
      ⟨_, _, _, _, _, _, hdown | hup⟩
    · omega
    · exact hdown.1
    · omega
  have hinv := h.codeInv
  rw [hcc] at hinv
  obtain ⟨hr, _, heq, hcode, hcanonlevel, hcanonlab, _, _⟩ :=
    processnode_fast (ctx := ctx) (level := current)
      (numcells := numcells) (st := st) ⟨hfirst, hneg⟩
  apply FrozenOut.mk current codes bs
  · rw [hcode, hcanonlevel, heq]
    exact hinv
  · exact hpath
  · exact hstem
  · rw [hcanonlab]
    exact h.incumbent
  · rw [heq, hr]
    exact hfloor

/-- Every negative off-path leaf prune is either comparison-frozen or a
jump to the saved cheap-cell boundary. -/
theorem pruneMode {G : Colored n k} {ctx : Ctx}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt} {best : Option Key} {trail : FrameTrail}
    (hn : ctx.n = n)
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
        (processnode ctx current numcells st).1 ∨
      (processnode ctx current numcells st).1 =
        Int.ofNat st.noncheaplevel - 1 := by
  have hr := (processnode_fast (ctx := ctx) (level := current)
    (numcells := numcells) (st := st) ⟨hfirst, hneg⟩).1
  rcases pruneReturn_split h.codeInv.eqlev_nonneg with hfloor | hjump
  · exact Or.inl (h.frozen hn hpath hstem hfirst hneg hfloor)
  · exact Or.inr (hr.trans hjump)

end RunPrep

end Hex.GraphIso.Nauty
