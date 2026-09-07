/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.HeadReturn
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- Every valid first-path node finishes at its parent. The induction
uses the recorded guiding visit, then the saved reference rules out every
premature return from its sibling tail. -/
theorem first_return {G : Colored n k} {ctx : Ctx n} (tcLevel : Nat)
    (hg : ctx.g = rowsOf G) :
    ∀ fuel level numcells (codes : List Nat) (st : SearchSt n) (trail : FrameTrail),
      FirstInv G ctx level codes numcells st trail →
      PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level st →
      st.noncheaplevel ≤ level →
      CheapDesc ctx level st.noncheaplevel (refine ctx level st.lab st.ptn st.active numcells) →
      OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
      1 ≤ level → level = codes.length + 1 → st.firsttc.size = n + 2 → n + 2 < level + fuel →
      (firstPathNode ctx (n + 2) tcLevel fuel level numcells st).1 = Int.ofNat level - 1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells codes st trail hfirst _ _ _ _ _ _ _ hfuel
    have := hfirst.searchOk.levelLe
    omega
  | succ fuel ih =>
    intro level numcells codes st trail hfirst hpathOk hcheap hdesc horb hlevel hpath htcsize hfuel
    have hn0 : 0 < n := by have := hfirst.searchOk.levelLe; omega
    let rs := refine ctx level st.lab st.ptn st.active numcells
    by_cases hnum : rs.numcells = n
    · rw [firstPath_discrete_state ctx (n + 2) tcLevel fuel level numcells st hnum]
    · obtain ⟨hit, heqt, hcount⟩ := hfirst.refined hg hn0 hlevel
      have hnumLt : rs.numcells < n :=
        Nat.lt_of_le_of_ne (hcount ▸ bcount_le _ _ _) hnum
      have hl := hfirst.searchOk.levelLe
      obtain ⟨tc, len, hlen, hrange, hmk, hhead⟩ := hfirst.head
        (runFuel := fuel) (specFuel := n - level) hg rfl hlevel hpath (by omega) (by omega)
        hcheap hdesc hpathOk horb hnumLt
      let cell := windowSet n rs.lab tc len
      let pre := firstStart ctx level numcells tc len st
      have htcPre : pre.firsttc.size = n + 2 := by
        dsimp only [pre, firstStart]
        split <;> simpa only [Array.size_set!] using htcsize
      have hdone := hhead.complete (tcLevel := tcLevel) hg rfl
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by omega) htcPre (fun child childTrail hfc hpc hnc hdc hoc htc => by
          have h := ih (level + 1) (rs.numcells + 1) (codes ++ [rs.longcode]) child childTrail
            hfc hpc hnc hdc hoc (by omega)
            (by simp only [List.length_append, List.length_singleton]; omega) htc (by omega)
          exact h.trans (by simp only [Int.ofNat_eq_natCast]; omega))
      rw [firstPath_internal_state ctx (n + 2) tcLevel fuel level numcells st hnum, hmk]
      dsimp only
      rw [worksetOf_eq_windowSet _ tc len (by omega)]
      change (match (firstChildLoop ctx (n + 2) tcLevel fuel (n + 1) level rs.numcells tc
          ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 pre).1 with
        | some r => (r, (firstChildLoop ctx (n + 2) tcLevel fuel (n + 1) level rs.numcells tc
            ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 pre).2.2)
        | none => (Int.ofNat level - 1, firstFinish level len
            (firstChildLoop ctx (n + 2) tcLevel fuel (n + 1) level rs.numcells tc
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 pre).2.1
            (firstChildLoop ctx (n + 2) tcLevel fuel (n + 1) level rs.numcells tc
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell 0 pre).2.2)).1 = _
      rw [hdone]

end Hex.GraphIso.Nauty.Generation
