/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeComplete
import all HexGraphIso.Nauty.Search

public section

/-!
The first-path leaf: the discrete arm of `firstPathNode` installs the
first leaf and carries every fact the enclosing sweep needs.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Installing the first leaf leaves the orbit ledger, the coset cursor
and the cheap-cell boundary alone. -/
theorem firstterminal_ledger (level : Nat) (st : SearchSt) :
    (firstterminal level st).orbits = st.orbits ∧
    (firstterminal level st).cosetindex = st.cosetindex ∧
    (firstterminal level st).noncheaplevel = st.noncheaplevel := by
  rw [firstterminal]
  simp only [Id.run_bind, Id.run_pure]
  simp

/-- The discrete first-path arm is total and carries the sweep facts. -/
theorem FirstInv.leafTotal {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hpath : level = codes.length + 1)
    (h : FirstInv G ctx level codes numcells st trail)
    (hsound : OrbSound (OrbConn st.genTrace.toList ctx.n) st.orbits ctx.n)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    ∃ fs outBest eventTrail,
      FirstRun G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
          numcells outBest trail eventTrail
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
        FirstKeep ctx level st
          (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2 fs
          outBest := by
  have hrun := h.terminalRun (inf := inf) (tcLevel := tcLevel)
    (specFuel := specFuel) (fuel := fuel) hn hn0 hpath hnum
  dsimp only at hrun
  refine ⟨_, _, trail, hrun, ?_⟩
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  obtain ⟨horb, hcoset, hncl⟩ :=
    firstterminal_ledger level (firstLeafSt ctx level numcells st)
  have hgen := (firstterminal_store level
    (firstLeafSt ctx level numcells st)).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    cases hb
    rw [firstterminal_firstlab]
    exact keyLe_refl _
  · rw [horb, hgen]
    exact hsound
  · intro hc
    rw [hcoset]
    exact hc
  · intro _
    exact hncl
  · rw [(firstterminal_state level _).2.2.1]
    exact Nat.le_refl _

end Hex.GraphIso.Nauty
