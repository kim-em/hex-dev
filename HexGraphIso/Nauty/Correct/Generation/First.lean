/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Prefix
public import HexGraphIso.Nauty.Correct.Generation.Leaf
public import HexGraphIso.Nauty.Correct.Generation.Prune
public import HexGraphIso.Nauty.Correct.Generation.Agreement
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Refine

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat}

/-- The unique first descent installs a reference that actually occurs
below its entry, with all refinement codes and target hints intact. The all-same boundary
never crosses the frame being completed. -/
private theorem first_reference_data {G : Colored n k} {ctx : Ctx n} (inf tcLevel : Nat)
    (hg : ctx.g = rowsOf G) :
    ∀ fuel level numcells (codes : List Nat) (st : SearchSt n) (trail : FrameTrail),
      FirstInv G ctx level codes numcells st trail →
      1 ≤ level → level = codes.length + 1 → st.firsttc.size = n + 2 → n < level + fuel →
      ∃ targets key,
        HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key ∧
        Matches ctx level (firstPathNode ctx inf tcLevel fuel level numcells st).2 targets key ∧
        level ≤ (firstPathNode ctx inf tcLevel fuel level numcells st).2.allsamelevel ∧
        level ≤ (firstPathNode ctx inf tcLevel fuel level numcells st).2.eqlevFirst := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells codes st trail hfirst _ _ _ hfuel
    have := hfirst.searchOk.levelLe
    omega
  | succ fuel ih =>
    intro level numcells codes st trail hfirst hlevel hpath htcsize hfuel
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
      obtain ⟨hl, hm, _⟩ := first_leaf (inf := inf) (tcLevel := tcLevel) (fuel := fuel)
        hnum hfirst.codes.firstSize hfirst.searchOk.levelLe hdisc
      refine ⟨[], _, hl, hm, ?_⟩
      rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
      simp only [firstterminal, Id.run_bind, Id.run_pure]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
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
      have hpcode : pre.firstcode = st.firstcode.set! level rs.longcode := by dsimp only [pre]; split <;> rfl
      have hptc : pre.firsttc = st.firsttc.set! level (Int.ofNat tc) := by dsimp only [pre]; split <;> rfl
      let tcell := windowSet n rs.lab tc len
      obtain ⟨tv, hnext⟩ := nextElem_windowSet_some (lab := rs.lab) (tc := tc) (len := len)
        (by omega) (hit.ok.labOk _ (by rw [hit.ok.labSize]; omega))
      have hmem := (mem_windowSet.mp (VSet.nextElem_mem hnext)).2
      obtain ⟨o, ho, hat⟩ := mem_segN_iff.mp hmem
      have htv : tv < n := VSet.mem_lt (VSet.nextElem_mem hnext)
      have hrep : (pre.orbits[tv]! == tv) = true := by
        have horb : pre.orbits = st.orbits := by dsimp only [pre]; split <;> rfl
        rw [horb, hfirst.orbitId tv htv]
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
      obtain ⟨targets, key, hleaf, hmatches, hfloor, hagree⟩ := ih (level + 1) (rs.numcells + 1) full child childTrail
        hchild (by omega) (by simp only [full, List.length_append, List.length_singleton]; omega)
        hctc (by omega)
      have hocc : HasLeaf ctx tcLevel (level + 1) (childSt ctx level rs tc tv) targets key := by
        change HasLeaf ctx tcLevel (level + 1)
          (refine ctx (level + 1) (breakout n pre.lab pre.ptn (level + 1) tc tv).1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.1
            (breakout n pre.lab pre.ptn (level + 1) tc tv).2.2 (rs.numcells + 1)) targets key at hleaf
        rw [hplab, hpptn, breakout_ptn] at hleaf
        exact hleaf
      have hchildPrefix := first_prefix ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child level (by omega)
      have hcode : rs.longcode = (firstPathNode ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child).2.firstcode[level]! := by
        rw [hchildPrefix.1]
        change rs.longcode = pre.firstcode[level]!
        rw [hpcode, Array.getElem!_set!_self _ _ _ (by rw [hfirst.codes.firstSize]; omega)]
      have htc : Int.ofNat tc = (firstPathNode ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child).2.firsttc[level]! := by
        rw [hchildPrefix.2]
        change Int.ofNat tc = pre.firsttc[level]!
        rw [hptc, Array.getElem!_set!_self _ _ _ (by rw [htcsize]; omega)]
      have hmatchesParent := hmatches.cons hcode htc
      have hecell : (tc, tc + len - 1) ∈ cells rs.ptn level n :=
        isCell_mem_cells hcell (by rw [hit.ok.ptnSize]; exact Nat.le_refl _) hit.ok.ptnEnd (by omega)
      have hparent := HasLeaf.step hlt hecell (by omega) (by omega) htarget (hat ▸ hocc)
      refine ⟨tc :: targets, ⟨rs.longcode :: key.codes, key.rows⟩, hparent, ?_⟩
      have hfields := firstGuide_fields (ctx := ctx) (inf := inf) (tcLevel := tcLevel) (fuel := fuel)
        (cfuel := n) (level := level) (numcells := rs.numcells) (tc := tc) (tv := tv)
        (index := 0) (tcell := tcell) (st := pre) hrep (rfl : firstPathNode ctx inf tcLevel fuel
          (level + 1) (rs.numcells + 1) child = _)
      have haloop := firstGuide_agreement (ctx := ctx) (inf := inf) (tcLevel := tcLevel)
        (fuel := fuel) (cfuel := n) (level := level) (numcells := rs.numcells) (tc := tc)
        (tv := tv) (index := 0) (tcell := tcell) (st := pre) hrep
        (rfl : firstPathNode ctx inf tcLevel fuel (level + 1) (rs.numcells + 1) child = _)
        (Nat.le_trans (Nat.le_succ _) hagree)
      have hmloop := hfields.matching hmatchesParent
      have hfloop : level ≤ (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc tv
          (some tv) tcell 0 pre).2.2.allsamelevel := by
        rw [hfields.same]
        exact Nat.le_trans (Nat.le_succ _) hfloor
      rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
      rw [hmk]
      dsimp only
      rw [worksetOf_eq_windowSet _ tc len (by omega), hnext]
      let loop := firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc tv
        (some tv) tcell 0 pre
      let out := (match loop.1 with
        | some r => (r, loop.2.2)
        | none => (Int.ofNat level - 1, firstFinish level len loop.2.1 loop.2.2)).2
      change Matches ctx level out (tc :: targets) ⟨rs.longcode :: key.codes, key.rows⟩ ∧
        level ≤ out.allsamelevel ∧ level ≤ out.eqlevFirst
      dsimp only [out, loop]
      generalize he : firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells tc tv
        (some tv) tcell 0 pre = result at hmloop hfloop haloop ⊢
      obtain ⟨r, index, out⟩ := result
      cases r with
      | some r => exact ⟨hmloop, hfloop, haloop⟩
      | none =>
        dsimp only
        refine ⟨?_, finish_floor hfloop, ?_⟩
        · unfold firstFinish
          split <;> exact hmloop.stateEq rfl rfl rfl
        · unfold firstFinish
          split <;> exact haloop


/-- The unique first descent installs a reference that actually occurs
below its entry, preserving its codes, target hints and all-same boundary. -/
theorem first_reference {G : Colored n k} {ctx : Ctx n} (inf tcLevel : Nat)
    (hg : ctx.g = rowsOf G)
    (fuel level numcells : Nat) (codes : List Nat) (st : SearchSt n) (trail : FrameTrail)
    (hfirst : FirstInv G ctx level codes numcells st trail)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (htcsize : st.firsttc.size = n + 2) (hfuel : n < level + fuel) :
    ∃ targets key,
      HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells) targets key ∧
      Matches ctx level (firstPathNode ctx inf tcLevel fuel level numcells st).2 targets key ∧
      level ≤ (firstPathNode ctx inf tcLevel fuel level numcells st).2.allsamelevel := by
  obtain ⟨targets, key, hp, hm, hs, _⟩ :=
    first_reference_data inf tcLevel hg fuel level numcells codes st trail hfirst hlevel hpath htcsize hfuel
  exact ⟨targets, key, hp, hm, hs⟩

/-- The first descent establishes agreement through its entry level.
This records the actual comparison depth, which cannot be recovered from
the weaker prefix invariant alone. -/
theorem first_agreement {G : Colored n k} {ctx : Ctx n} (inf tcLevel : Nat)
    (hg : ctx.g = rowsOf G)
    (fuel level numcells : Nat) (codes : List Nat) (st : SearchSt n) (trail : FrameTrail)
    (hfirst : FirstInv G ctx level codes numcells st trail)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (htcsize : st.firsttc.size = n + 2) (hfuel : n < level + fuel) :
    level ≤ (firstPathNode ctx inf tcLevel fuel level numcells st).2.eqlevFirst := by
  obtain ⟨_, _, _, _, _, ha⟩ :=
    first_reference_data inf tcLevel hg fuel level numcells codes st trail hfirst hlevel hpath htcsize hfuel
  exact ha

end Hex.GraphIso.Nauty.Generation
