/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.First
public import HexGraphIso.Nauty.Correct.Generation.Uniform
public import HexGraphIso.Nauty.Correct.Certify
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Refine

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

set_option maxHeartbeats 1600000 in
/-- When the first descent lowers its all-same boundary to the current
frame, every leaf below that frame has the same codes, target hints, and
adjacency rows. The proof follows the actual orbit counter. -/
theorem first_uniform {G : Colored n k} {ctx : Ctx n} (tcLevel : Nat)
    (hg : ctx.g = rowsOf G) :
    ∀ fuel level numcells (codes : List Nat) (st : SearchSt n) (trail : FrameTrail),
      FirstInv G ctx level codes numcells st trail →
      PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
        (initialPartition G).1 level st →
      st.noncheaplevel ≤ level →
      CheapDesc ctx level st.noncheaplevel (refine ctx level st.lab st.ptn st.active numcells) →
      OrbSound (OrbConn st.genTrace.toList n) st.orbits n →
      1 ≤ level → level = codes.length + 1 → st.firsttc.size = n + 2 → n + 2 < level + fuel →
      (firstPathNode ctx (n + 2) tcLevel fuel level numcells st).2.allsamelevel ≤ level →
      ∃ targets key, Uniform ctx tcLevel level
        (refine ctx level st.lab st.ptn st.active numcells) targets key := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells codes st trail hfirst _ _ _ _ _ _ _ hfuel
    have := hfirst.searchOk.levelLe
    omega
  | succ fuel ih =>
    intro level numcells codes st trail hfirst hpathOk hcheap hdesc horb hlevel hpath htcsize hfuel hsame
    have hn : 0 < n := by have := hfirst.searchOk.levelLe; omega
    obtain ⟨hit, heqt, hcount⟩ := hfirst.refined hg hn hlevel
    let rs := refine ctx level st.lab st.ptn st.active numcells
    by_cases hnum : rs.numcells = n
    · have hdisc : ∀ q, q < n → rs.ptn[q]! ≤ level := by
        have hc : List.countP (fun q => decide (rs.ptn[q]! ≤ level)) (List.range n) =
            (List.range n).length := by
          rw [List.length_range]
          exact hcount.trans hnum
        intro q hq
        simpa using List.countP_eq_length.mp hc q (List.mem_range.mpr hq)
      exact ⟨[], _, Uniform.leaf hit hdisc⟩
    · have hbc : bcount rs.ptn level n < n := by
        rw [hcount]
        exact Nat.lt_of_le_of_ne (hcount ▸ bcount_le _ _ _) hnum
      obtain ⟨tc, len, hmk, hcell, hlen, hrange⟩ :=
        maketargetcell_open (ctx := ctx) (tcLevel := tcLevel) (hint := -1)
          (lab := rs.lab) hlevel hit.ok.ptnSize hit.ok.ptnEnd hbc
      have hspec := maketargetcell_eq_spec (tcLevel := tcLevel) heqt hit.ok.labOk
        hit.ok.labSize hit.ok.ptnSize hit.ok.ptnEnd
      have htarget : tc = specTargetcell ctx rs.lab rs.ptn level tcLevel := by
        have h := congrArg Prod.fst (hspec.symm.trans hmk)
        exact h.symm
      have hlt : level < n := by
        have hok := refine_searchOk hn hfirst.searchOk hlevel
          (st2 := firstLeafSt ctx level numcells st) rfl rfl (Or.inl rfl)
        have hle := hok.bc
        change level ≤ bcount rs.ptn level n at hle
        omega
      let pre0 : SearchSt n := { st with
        lab := rs.lab, ptn := rs.ptn, active := rs.active,
        firstcode := st.firstcode.set! level rs.longcode,
        firsttc := st.firsttc.set! level (Int.ofNat tc),
        numnodes := st.numnodes + 1, tctotal := st.tctotal + len }
      let pre := if pre0.noncheaplevel ≥ level ∧ ¬ cheapautom pre0.ptn level n then
        { pre0 with noncheaplevel := level + 1 } else pre0
      have hplab : pre.lab = rs.lab := by dsimp only [pre]; split <;> rfl
      have hpptn : pre.ptn = rs.ptn := by dsimp only [pre]; split <;> rfl
      have hptc : pre.firsttc = st.firsttc.set! level (Int.ofNat tc) := by dsimp only [pre]; split <;> rfl
      have hpncl : pre.noncheaplevel = if st.noncheaplevel ≥ level ∧
          ¬ cheapautom rs.ptn level n = true then level + 1 else st.noncheaplevel := by
        dsimp only [pre, pre0]
        split <;> rfl
      let tcell := windowSet n rs.lab tc len
      obtain ⟨tv, hnext⟩ := nextElem_windowSet_some (lab := rs.lab) (tc := tc) (len := len)
        (by omega) (hit.ok.labOk _ (by rw [hit.ok.labSize]; omega))
      have hmem := (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
      obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp hmem
      have htv : tv < n := VSet.mem_lt (VSet.nextElem_mem hnext)
      have hrep : (pre.orbits[tv]! == tv) = true := by
        have horbits : pre.orbits = st.orbits := by dsimp only [pre]; split <;> rfl
        rw [horbits, hfirst.orbitId tv htv]
        simp
      have hatPre : pre.lab[tc + o]! = tv := by rw [hplab]; exact hat
      let child : SearchSt n := { pre with
        lab := (breakout n pre.lab pre.ptn (level + 1) tc tv).1
        ptn := (breakout n pre.lab pre.ptn (level + 1) tc tv).2.1
        active := (breakout n pre.lab pre.ptn (level + 1) tc tv).2.2
        fixedpts := pre.fixedpts.insert tv
        cosetindex := tv }
      let full := codes ++ [rs.longcode]
      let childTrail := trail.push level ⟨sweepFrame 0 full rs.lab rs.ptn tc rs.numcells, o⟩
      have hchild : FirstInv G ctx (level + 1) full (rs.numcells + 1) child childTrail := by
        have h := hfirst.child (specFuel := 0) hg hn hpath hlt hcell hlen hrange ho
        dsimp only at h
        change FirstInv G ctx (level + 1) full (rs.numcells + 1)
          { pre with
            lab := (breakout n pre.lab pre.ptn (level + 1) tc pre.lab[tc + o]!).1,
            ptn := (breakout n pre.lab pre.ptn (level + 1) tc pre.lab[tc + o]!).2.1,
            active := (breakout n pre.lab pre.ptn (level + 1) tc pre.lab[tc + o]!).2.2,
            fixedpts := pre.fixedpts.insert pre.lab[tc + o]!, cosetindex := pre.lab[tc + o]! }
          childTrail at h
        rwa [hatPre] at h
      have hctc : child.firsttc.size = n + 2 := by
        change pre.firsttc.size = n + 2
        rw [hptc, Array.size_set!, htcsize]
      have hchildPath : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
          (initialPartition G).1 (level + 1) child := by
        have h := hfirst.childPath hg hn hpath hpathOk hcell hlen hrange ho
        dsimp only at h
        rw [hatPre] at h
        exact h
      have hchildCheap : child.noncheaplevel ≤ level + 1 := by
        change pre.noncheaplevel ≤ level + 1
        rw [hpncl]
        split <;> omega
      have hchildDesc : CheapDesc ctx (level + 1) child.noncheaplevel
          (refine ctx (level + 1) child.lab child.ptn child.active (rs.numcells + 1)) := by
        have hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u := by
          rw [hg]; exact rowsOf_symm G
        have h := hdesc.child hit heqt hcount hsymm hlt hcell hlen hrange ho
        dsimp only at h
        rw [hat] at h
        change CheapDesc ctx (level + 1) pre.noncheaplevel
          (refine ctx (level + 1) (breakout n pre.lab pre.ptn (level + 1) tc tv).1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.2 (rs.numcells + 1))
        rw [breakout_ptn, hplab, hpptn, hpncl]
        exact h
      have hchildOrb : OrbSound (OrbConn child.genTrace.toList n) child.orbits n := by
        change OrbSound (OrbConn pre.genTrace.toList n) pre.orbits n
        dsimp only [pre]
        split <;> exact horb
      obtain ⟨_, _, _, _, hfloor⟩ := first_reference (n + 2) tcLevel hg fuel (level + 1)
        (rs.numcells + 1) full child childTrail hchild (by omega)
        (by simp only [full, List.length_append, List.length_singleton]; omega) hctc (by omega)
      have hfields := firstGuide_fields (ctx := ctx) (inf := n + 2) (tcLevel := tcLevel) (fuel := fuel)
        (cfuel := n) (level := level) (numcells := rs.numcells) (tc := tc) (tv := tv)
        (index := 0) (tcell := tcell) (st := pre) hrep (rfl : firstPathNode ctx (n + 2) tcLevel fuel
          (level + 1) (rs.numcells + 1) child = _)
      have hL := firstLoopTotal (tail := len - 1) (level := level)
        (specFuel := n - level) (runFuel := fuel) (cs := codes) (st := st)
        (numcells := numcells) (tc := tc) (len := len) (inf := n + 2)
        (tcLevel := tcLevel) (trail := trail) hg rfl hn
        (totalAll G ctx (n + 2) tcLevel fuel).1 (totalAll G ctx (n + 2) tcLevel fuel).2
        (by omega) (by omega) hlevel hpath hlt hfirst hpathOk hcheap hdesc horb
        hcell hlen hrange rfl (by omega)
      obtain ⟨_, _, _, _, _, _, last, hcounter⟩ := hL
      dsimp only at hcounter
      rw [hnext] at hcounter
      rw [firstPath_internal_state ctx (n + 2) tcLevel fuel level numcells st hnum,
        hmk] at hsame
      dsimp only at hsame
      rw [worksetOf_eq_windowSet _ tc len (by omega), hnext] at hsame
      let loop := firstChildLoop ctx (n + 2) tcLevel fuel (n + 1) level rs.numcells tc tv
        (some tv) tcell 0 pre
      have hboundary : len = loop.2.1 ∧
          (firstPathNode ctx (n + 2) tcLevel fuel (level + 1) (rs.numcells + 1) child).2.allsamelevel = level + 1 := by
        have hfl : level < loop.2.2.allsamelevel := by
          rw [hfields.same]
          omega
        change (match loop.1 with
          | some r => (r, loop.2.2)
          | none => (Int.ofNat level - 1, firstFinish level len loop.2.1 loop.2.2)).2.allsamelevel ≤ level at hsame
        cases he : loop.1 with
        | some r => simp only [he] at hsame; omega
        | none =>
          simp only [he] at hsame
          obtain ⟨hc, hs⟩ := finish_drop hfl hsame
          exact ⟨hc, hfields.same ▸ hs⟩
      obtain ⟨targets, key, hguide⟩ := ih (level + 1) (rs.numcells + 1) full child childTrail
        hchild hchildPath hchildCheap hchildDesc hchildOrb (by omega)
        (by simp only [full, List.length_append, List.length_singleton]; omega) hctc (by omega)
        (Nat.le_of_eq hboundary.2)
      have hguide' : Uniform ctx tcLevel (level + 1) (childSt ctx level rs tc tv) targets key := by
        change Uniform ctx tcLevel (level + 1)
          (refine ctx (level + 1) (breakout n pre.lab pre.ptn (level + 1) tc tv).1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.2 (rs.numcells + 1)) targets key at hguide
        rw [hplab, hpptn, breakout_ptn] at hguide
        exact hguide
      have hecell : (tc, tc + len - 1) ∈ cells rs.ptn level n :=
        isCell_mem_cells hcell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd (by omega)
      refine ⟨tc :: targets, ⟨rs.longcode :: key.codes, key.rows⟩,
        Uniform.carriers hit hlt (by rw [hg]; exact size_rowsOf G) hecell (by omega)
          htarget (by omega : o ≤ tc + len - 1 - tc) ?_ (hat ▸ hguide')⟩
      intro o' ho'
      have hc := hcounter.full (by rw [segN_length]; exact Nat.le_of_eq hboundary.1) _
        (mem_segN_iff.mpr ⟨o', by omega, rfl⟩)
      change ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab rs.ptn level rs.lab γ ∧ γ[rs.lab[tc + o']!]! = rs.lab[tc + o]!
      rw [hat]
      exact hc

end Hex.GraphIso.Nauty.Generation
