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

/-- Below a saved cheap-cell boundary, the current refined node remains in
the small-cell subtree generated at that boundary.  At the boundary itself
the implication is dormant until the executable guard either validates the
shape or parks the boundary at the child. -/
@[expose] def CheapDesc (ctx : Ctx n) (level boundary : Nat)
    (st : RefineSt n) : Prop :=
  boundary < level → SubtreeOk ctx level st

namespace CheapDesc

/-- A boundary created at the current node has no strict descendant
obligation yet. -/
theorem same (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    CheapDesc ctx level level st := by
  intro h
  omega

/-- At an entered sibling sweep, a saved boundary at or above the current
node supplies the small-cell subtree fact.  A strictly older boundary uses
the inherited descent invariant; equality is exactly the case in which the
current cheap-cell guard must have succeeded. -/
theorem atLevel {ctx : Ctx n} {level boundary : Nat} {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hle : boundary ≤ level)
    (hguard : boundary = level → cheapautom st.ptn level n = true) :
    SubtreeOk ctx level st := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heqBoundary
  · exact h hlt
  · exact subtreeOk_of_cheapautom hit heq hcount
      (hguard heqBoundary)

/-- The executable cheap-cell boundary update carries the small-cell
subtree invariant into every individualized child. -/
theorem child {ctx : Ctx n} {level boundary tc len o : Nat}
    {st : RefineSt n}
    (h : CheapDesc ctx level boundary st)
    (hit : IterOk ctx level st) (heq : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hlvl : level < n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    let boundary' := if boundary ≥ level ∧
        ¬cheapautom st.ptn level n then level + 1 else boundary
    CheapDesc ctx (level + 1) boundary'
      (childSt ctx level st tc st.lab[tc + o]!) := by
  dsimp only
  let boundary' := if boundary ≥ level ∧
      ¬cheapautom st.ptn level n then level + 1 else boundary
  intro hbelow
  have hparent : SubtreeOk ctx level st := by
    rcases Nat.lt_or_ge boundary level with hold | hge
    · exact h hold
    · have hcheap : cheapautom st.ptn level n = true := by
        rcases hc : cheapautom st.ptn level n with _ | _
        · have hguard : boundary ≥ level ∧
              ¬cheapautom st.ptn level n := ⟨hge, by simp [hc]⟩
          change (if boundary ≥ level ∧
            ¬cheapautom st.ptn level n then level + 1 else boundary) <
              level + 1 at hbelow
          rw [ite_eq_left hguard] at hbelow
          exfalso
          omega
        · rfl
      exact subtreeOk_of_cheapautom hit heq hcount hcheap
  exact subtreeOk_child hparent hlvl hsymm
    (mem_cells_of_isCell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _)
      hit.ok.ptnEnd hcell (by omega)
      (by rw [hit.ok.ptnSize]; exact hrange))
    (by omega) (by omega)

end CheapDesc

namespace FrozenOut

/-- Expose a shorter ancestor prefix while retaining the same frozen
comparison.  This is the transport used as an early return crosses nested
node and loop frames. -/
theorem shrink {ctx : Ctx n} {stem ancestor : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int}
    (h : FrozenOut ctx stem out best r)
    (hprefix : stem.take ancestor.length = ancestor) :
    FrozenOut ctx ancestor out best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  apply FrozenOut.mk current codes bestCodes hcode hdepth
  · have hlen := congrArg List.length hprefix
    simp only [List.length_take] at hlen
    have hle : ancestor.length ≤ stem.length := by omega
    calc
      codes.take ancestor.length =
          (codes.take stem.length).take ancestor.length := by
            rw [List.take_take, Nat.min_eq_left hle]
      _ = ancestor := by rw [hstem, hprefix]
  · exact hinstalled
  · exact hbest
  · exact hfloor

/-- Fixed-point cleanup changes none of a frozen comparison's fields. -/
theorem setFixed {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (fixedpts : VSet n) :
    FrozenOut ctx stem { out with fixedpts := fixedpts } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

/-- Resetting first-path return controls changes none of a frozen
comparison's fields. -/
theorem setFirst {ctx : Ctx n} {stem : List Nat} {out : SearchSt n}
    {best : Option (Key n)} {r : Int} (h : FrozenOut ctx stem out best r)
    (gcaFirst stabvertex : Nat) :
    FrozenOut ctx stem
      { out with gcaFirst := gcaFirst, stabvertex := stabvertex } best r := by
  rcases h with
    ⟨current, codes, bestCodes, hcode, hdepth, hstem, hinstalled, hbest,
      hfloor⟩
  exact .mk current codes bestCodes hcode hdepth hstem hinstalled hbest
    hfloor

end FrozenOut

namespace RunPrep

/-- A negative comparison branch whose prune tail stays below the recorded
divergence produces a frozen-code witness without changing the incumbent. -/
theorem frozen {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
    (h : RunPrep G ctx tcLevel current codes bs fs numcells st best trail)
    (hpath : current = codes.length)
    (hstem : codes.take stem.length = stem)
    (hfirst : st.eqlevFirst ≠ current) (hneg : st.compCanon < 0)
    (hfloor : Int.ofNat st.eqlevCanon.toNat ≤
      pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon) :
    FrozenOut ctx stem (processnode ctx current numcells st).2 best
      (processnode ctx current numcells st).1 := by
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
  · exact h.bestCodes
  · rw [hcanonlab]
    exact h.incumbent
  · rw [heq, hr]
    exact hfloor

/-- Every negative off-path leaf prune is either comparison-frozen or a
jump to the saved cheap-cell boundary. -/
theorem pruneMode {G : Colored n k} {ctx : Ctx n}
    {tcLevel current numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
   
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
  · exact Or.inl (h.frozen hpath hstem hfirst hneg hfloor)
  · exact Or.inr (hr.trans hjump)

end RunPrep

end Hex.GraphIso.Nauty
