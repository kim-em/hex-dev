/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Head
public import HexGraphIso.Nauty.Correct.Certify
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The existing first-path preparation, named for use in proofs. -/
@[expose] def firstStart (ctx : Ctx n) (level numcells tc len : Nat) (st : SearchSt n) : SearchSt n :=
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let pre : SearchSt n := { st with
    lab := rs.lab, ptn := rs.ptn, active := rs.active,
    firstcode := st.firstcode.set! level rs.longcode,
    firsttc := st.firsttc.set! level (Int.ofNat tc),
    numnodes := st.numnodes + 1, tctotal := st.tctotal + len }
  if pre.noncheaplevel ≥ level ∧ ¬ cheapautom pre.ptn level n then
    { pre with noncheaplevel := level + 1 } else pre

end Generation

open Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- The established correctness induction exposes the actual guiding
visit and recovered tail at an internal first-path node. -/
theorem FirstInv.head {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + 1 + specFuel = n + 1)
    (hfuel : n + 2 < level + 1 + runFuel)
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hfirst : FirstInv G ctx level codes numcells st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells < n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    ∃ tc len,
      let tcell := windowSet n rs.lab tc len
      2 ≤ len ∧ tc + len ≤ n ∧
      maketargetcell ctx rs.lab rs.ptn level tcLevel (-1) =
        (tc, worksetOf n rs.lab tc (tc + len - 1), len) ∧
      FirstHead G ctx inf tcLevel specFuel runFuel level rs.numcells tc len
        ((tcell.nextElem none).getD 0) st.noncheaplevel full rs.lab rs.ptn tcell
        (firstStart ctx level numcells tc len st) trail := by
  intro rs full
  have hn0 : 0 < n := by have := hfirst.searchOk.levelLe; omega
  obtain ⟨hit, heqt, hcount⟩ := hfirst.refined hg hn0 hlevel
  have hbc : bcount rs.ptn level n < n := by rw [hcount]; exact hnum
  obtain ⟨tc, len, hmk, hcell, hlen, hrange⟩ :=
    maketargetcell_open (ctx := ctx) (tcLevel := tcLevel) (hint := -1)
      (lab := rs.lab) hlevel hit.ok.ptnSize hit.ok.ptnEnd hbc
  have hlt : level < n := by
    have hok := refine_searchOk hn0 hfirst.searchOk hlevel
      (st2 := firstLeafSt ctx level numcells st) rfl rfl (Or.inl rfl)
    have hb := hok.bc
    change level ≤ bcount rs.ptn level n at hb
    omega
  obtain ⟨_, _, _, _, _, hhead, _⟩ :=
    firstLoopTotal (tail := len - 1) (level := level) (specFuel := specFuel)
      (runFuel := runFuel) (cs := codes) (st := st) (numcells := numcells)
      (tc := tc) (len := len) (inf := inf) (tcLevel := tcLevel) (trail := trail)
      hg hinf hn0 (totalAll G ctx inf tcLevel runFuel).1 (totalAll G ctx inf tcLevel runFuel).2
      hfuel hspec hlevel hpath hlt hfirst hpathOk hcheap hdesc horb hcell hlen hrange rfl (by omega)
  exact ⟨tc, len, hlen, hrange, hmk, hhead⟩

end Hex.GraphIso.Nauty
