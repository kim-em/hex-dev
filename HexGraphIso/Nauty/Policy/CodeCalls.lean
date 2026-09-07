/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.ReturnCodes
public import HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.Fuel
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.ReturnCodes
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Node preparation advances both code machines by the actual refinement
code and preserves the incoming semantic incumbent. -/
theorem Comparison.prepare {ctx : Ctx n} {tcLevel numcells : Nat}
    {cs bs fs : List Nat} {st : Search n} (h : Comparison ctx cs bs fs st)
    (hlen : cs.length ≤ n) :
    let p := prepareOther ctx tcLevel (cs.length + 1) numcells st
    Comparison ctx (cs ++ [p.2.1]) bs fs p.2.2.2.2.2 ∧
      p.2.2.2.2.2.key ctx bs = st.key ctx bs := by
  have hc := refine_longcode_lt ctx (cs.length + 1) st.lab st.ptn st.active numcells
  change (Engine.visit ctx (cs.length + 1) numcells st).2.1 < codeSentinel at hc
  refine ⟨?_, ?_⟩
  · have hm := ((h.visit (cs.length + 1) numcells).compare hc hlen).target tcLevel
      (Engine.visit ctx (cs.length + 1) numcells st).1
    simpa only [prepareOther, List.length_append, List.length_singleton] using hm
  · unfold prepareOther
    rw [chooseTarget_fields]
    have hl := (compareCodes_frame (cs.length + 1)
      (Engine.visit ctx (cs.length + 1) numcells st).2.1
      (Engine.visit ctx (cs.length + 1) numcells st).2.2).2.2.2
    simp only [Search.key, hl]
    rfl

/-- Whole-call code comparisons retain the incoming path and monotonically
increase the incumbent. A positive sweep comparison requires a first child. -/
def codeContract (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat) : Generic.Contract (Search n) n where
  nodePre fuel first level numcells st :=
    first = false ∧ NodePre G ctx tcLevel level numcells st ∧ n + 1 ≤ level + fuel
  nodePost _ _ level _ st result := ∀ cs bs fs,
    cs.length + 1 = level → Comparison ctx cs bs fs st →
      ∃ bs', ReturnCodes ctx cs bs' fs result.2 ∧ Generic.Grows (st.key ctx bs) (result.2.key ctx bs')
  sweepPre fuel cfuel first level numcells tc tv1 cursor cell _ st :=
    SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st ∧
      n ≤ level + fuel ∧ Generic.CursorFuel n cfuel cursor
  sweepPost _ _ first level _ _ _ cursor _ _ st result := ∀ cs bs fs,
    cs.length = level → Comparison ctx cs bs fs st →
      (st.compCanon ≤ 0 ∨ first = false ∧ cursor.isSome) →
        ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows (st.key ctx bs) (result.2.2.key ctx bs')

/-- An off-path node settles its comparison at a leaf or through the
first child of its sweep, then retains that result through its return. -/
theorem codes_node {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hnext : (codeContract G ctx tcLevel).sweepValid fuel (n + 1) next)
    (cs bs fs : List Nat) (numcells : Nat) (st : Search n)
    (hin : NodePre G ctx tcLevel (cs.length + 1) numcells st)
    (hfuel : n + 1 ≤ cs.length + 1 + (fuel + 1))
    (hc : Comparison ctx cs bs fs st) :
    let result := Generic.nodeStep ctx tcLevel next false (cs.length + 1) numcells st
    ∃ bs', ReturnCodes ctx cs bs' fs result.2 ∧ Generic.Grows (st.key ctx bs) (result.2.key ctx bs') := by
  have hlen : cs.length ≤ n := by
    have hbc := hin.partition.bc
    change cs.length + 1 ≤ bcount st.ptn (cs.length + 1) n at hbc
    have := bcount_le st.ptn (cs.length + 1) n
    omega
  have hp := hin.prepare hn0 hgsz hsymm hloop
  have hm := hc.prepare (tcLevel := tcLevel) (numcells := numcells) hlen
  have hphase := hin.phase hn0
  dsimp only [prepareOther] at hp hm hphase
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.compareCodes, Generic.Policy.chooseTarget,
    Generic.Policy.classify, Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hv : visit ctx (cs.length + 1) numcells st = r at hp hm hphase ⊢
  obtain ⟨nc, code, refined⟩ := r
  simp only [Bool.false_eq_true, ite_false]
  dsimp only at hp hm hphase
  generalize ht : chooseTarget false ctx tcLevel (cs.length + 1) nc
    (compareCodes (cs.length + 1) code refined) = t at hp hm hphase ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  obtain ⟨hok, hi, hh, _, hready⟩ := hp
  obtain ⟨hm, hk⟩ := hm
  have hfinish : ∀ out, (∃ bs', ReturnCodes ctx (cs ++ [code]) bs' fs out ∧
      Generic.Grows (targeted.key ctx bs) (out.key ctx bs')) →
      ∃ bs', ReturnCodes ctx cs bs' fs out ∧ Generic.Grows (st.key ctx bs) (out.key ctx bs') := by
    intro out hout
    obtain ⟨bs', hr, hg⟩ := hout
    exact ⟨bs', hr.prefix ⟨[code], rfl⟩, hk ▸ hg⟩
  by_cases hleaf : (classify ctx (cs.length + 1) nc targeted).1 = .internal
  · rw [classify_internal_state hleaf]
    rw [show leafExit .internal (cs.length + 1) targeted = (.done, targeted) from rfl]
    dsimp only
    have hph : (cheapCheck false (cs.length + 1) targeted).compCanon ≤ 0 ∨
        false = false ∧ (cell.nextElem none).isSome := by
      rcases hphase hleaf with hc | hn
      · left
        unfold cheapCheck
        split <;> exact hc
      · exact Or.inr ⟨rfl, hn⟩
    have hn := hnext false (cs.length + 1) nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck false (cs.length + 1) targeted)
      ⟨hready hleaf, by omega, fun _ _ => by omega⟩ (cs ++ [code]) bs fs
      (by simp) (by simpa only [List.length_append, List.length_singleton] using hm.cheap false (cs.length + 1)) hph
    generalize hs : next false (cs.length + 1) nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (cheapCheck false (cs.length + 1) targeted) = result at hn ⊢
    obtain ⟨exit, index, out⟩ := result
    have hgkey : (cheapCheck false (cs.length + 1) targeted).key ctx bs = targeted.key ctx bs := by
      unfold cheapCheck
      split <;> rfl
    rw [hgkey] at hn
    cases exit with
    | fuel => exact hfinish out hn
    | unwind => exact hfinish out hn
    | done =>
      obtain ⟨bs', hr, hg⟩ := hn
      apply hfinish
      exact ⟨bs', hr.afterSweep false (cs.length + 1) size index,
        by change Generic.Grows (targeted.key ctx bs)
             ((afterSweep false (cs.length + 1) size index out).key ctx bs'); rwa [afterSweep_key]⟩
  · have hh' : History ctx tcLevel (cs ++ [code]).length (cs ++ [code]).length nc targeted := by
      simpa only [List.length_append, List.length_singleton] using hh
    have hok' : SearchOk G (cs ++ [code]).length nc targeted.view := by
      simpa only [List.length_append, List.length_singleton] using hok
    have hl' : (classify ctx (cs ++ [code]).length nc targeted).1 ≠ .internal := by
      simpa only [List.length_append, List.length_singleton] using hleaf
    have hr := hm.exit_returned hh' hi hn0 (by simp) hok' hgsz hsymm hloop hl'
    simp only [List.length_append, List.length_singleton] at hr
    have hnot : (leafExit (classify ctx (cs.length + 1) nc targeted).1 (cs.length + 1)
      (classify ctx (cs.length + 1) nc targeted).2).1 ≠ .done :=
      fun he => hleaf ((leafExit_done _ _ _).mp he)
    generalize hcval : classify ctx (cs.length + 1) nc targeted = c at hr hnot ⊢
    obtain ⟨leaf, classified⟩ := c
    generalize heval : leafExit leaf (cs.length + 1) classified = result at hr hnot ⊢
    obtain ⟨exit, out⟩ := result
    cases exit with
    | done => exact (hnot rfl).elim
    | fuel => exact hfinish out hr
    | unwind => exact hfinish out hr

/-- A returned child either passes its settled comparison outward or
recovers it before the next surviving sibling. -/
theorem codes_advance {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hnext : (codeContract G ctx tcLevel).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (out : Search n) (exit : Exit)
    (cs bs fs : List Nat) (before : Option (Key n)) (hlen : cs.length = level)
    (hcodes : ReturnCodes ctx cs bs fs out) (hgrows : Generic.Grows before (out.key ctx bs))
    (hfuel : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1))
    (hready : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell
      (recoverLevels level (recoverPtn (n + 2) level out))) :
    let result := Generic.advance (n + 2) next first level numcells tc tv1 tv cell index out exit
    ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows before (result.2.2.key ctx bs') := by
  unfold Generic.advance
  dsimp only [policy, Generic.Policy.shortprune]
  have hcomp : Comparison ctx cs bs fs (recoverLevels level (recoverPtn (n + 2) level out)) := by
    simpa only [hlen] using hcodes.recover (n + 2)
  have hnonpos : (recoverLevels level (recoverPtn (n + 2) level out)).compCanon ≤ 0 :=
    recover_nonpos hcodes.nonpos (n + 2) level
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      let result := next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller
        (if first && (recoverLevels level (recoverPtn (n + 2) level out)).orbits[tv]! == tv1
          then index + 1 else index)
        (recoverLevels level (recoverPtn (n + 2) level out))
      ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows before (result.2.2.key ctx bs') := by
    intro smaller hsub
    obtain ⟨bs', hr, hg⟩ := hnext first level numcells tc tv1 (smaller.nextElem (some tv)) smaller _ _
      ⟨hready.next hsub, hfuel, Generic.CursorFuel.next hcursor⟩ cs bs fs hlen hcomp (Or.inl hnonpos)
    rw [recover_key] at hg
    exact ⟨bs', hr, hgrows.trans hg⟩
  have hlong : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      let result := Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index out
      ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows before (result.2.2.key ctx bs') := by
    intro smaller hsub
    unfold Generic.resume
    dsimp only [policy, Generic.Policy.longprune, Generic.Policy.recover, Generic.Policy.orbit]
    split
    · exact hcontinue _ (fun v hv => hsub v (Nauty.longprune_subset hv))
    · exact hcontinue _ hsub
  cases exit with
  | fuel => exact ⟨bs, hcodes, hgrows⟩
  | done => exact hlong cell (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact ⟨bs, hcodes, hgrows⟩
    · cases short with
      | false =>
        simpa only [Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong cell (fun _ hv => hv)
      | true =>
        simpa only [ite_true, Id.run_pure, apply_ite Id.run,
          apply_ite Prod.snd] using hlong (shortprune cell out)
          (fun v hv => Nauty.shortprune_subset (st := out.view) hv)

/-- The actual off-path child settles both comparisons. Skipping an
orbit representative is allowed only after a preceding child settled them. -/
theorem codes_sweep {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    {next : Generic.SweepFn (Search n) n}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hdescend : (codeContract G ctx tcLevel).nodeValid fuel (Generic.nodeCall ctx (n + 2) tcLevel fuel))
    (hnext : (codeContract G ctx tcLevel).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : Search n)
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 (some tv) cell st)
    (hfuel : n ≤ level + fuel) (hcursor : n ≤ tv + (cfuel + 1))
    (cs bs fs : List Nat) (hlen : cs.length = level) (hc : Comparison ctx cs bs fs st)
    (hphase : st.compCanon ≤ 0 ∨ first = false ∧ (some tv).isSome) :
    let result := Generic.sweepStep (n + 2) (Generic.nodeCall ctx (n + 2) tcLevel fuel)
      next first level numcells tc tv1 tv cell index st
    ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows (st.key ctx bs) (result.2.2.key ctx bs') := by
  have hpast : first = true → tv1 < tv := fun hf => hin.past hf tv rfl
  have hflag : (first && tv == tv1) = false := by
    cases first with
    | false => rfl
    | true =>
      have := hpast rfl
      simp only [Bool.true_and, beq_eq_false_iff_ne]
      omega
  have hnodePre := hin.child hn0 hgsz hsymm
  have hd := hdescend false (level + 1) (numcells + 1) (child first level tc tv st)
    ⟨rfl, hnodePre, by omega⟩ cs bs fs (by omega) (hc.child first level tc tv)
  change ∃ bs', ReturnCodes ctx cs bs' fs
      (Generic.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1) (child first level tc tv st)).2 ∧
    Generic.Grows ((child first level tc tv st).key ctx bs)
      ((Generic.node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
        (child first level tc tv st)).2.key ctx bs') at hd
  rw [← node_eq_generic] at hd
  have hstored := node_safe (fuel := fuel) hn0 hgsz hsymm hloop hnodePre
  have hready := hin.restore hn0 hgsz hsymm hstored
  have hkey : (child first level tc tv st).key ctx bs = st.key ctx bs := by
    cases first <;> rfl
  rw [hkey] at hd
  unfold Generic.sweepStep
  dsimp only [Generic.nodeCall, policy, Generic.Policy.child, Generic.Policy.afterChildFirst,
    Generic.Policy.leaveChild, Generic.Policy.orbit, Generic.Policy.shortprune,
    Generic.Policy.longprune, Generic.Policy.recover]
  simp only [hflag, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run, apply_ite Prod.snd]
  split
  · rw [← node_eq_generic]
    generalize hcall : node false ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child first level tc tv st) = result at hd hready ⊢
    obtain ⟨exit, out⟩ := result
    obtain ⟨bs', hr, hg⟩ := hd
    exact codes_advance hnext first level numcells tc tv1 tv index cell
      { out with fixedpts := out.fixedpts.erase tv } exit cs bs' fs (st.key ctx bs)
      hlen (hr.leave tv) hg hfuel hcursor hready
  · rename_i hskip
    have hnonpos : st.compCanon ≤ 0 := by
      rcases hphase with hc | ⟨hf, _⟩
      · exact hc
      · simp only [hf, Bool.not_false, Bool.true_or] at hskip
        exact (hskip trivial).elim
    exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st
      ⟨hin.next (fun _ hv => hv), hfuel, Generic.CursorFuel.next hcursor⟩ cs bs fs hlen hc (Or.inl hnonpos)

/-- The shared recursion settles both code machines and never decreases
an installed incumbent on any sufficiently bounded off-path call. -/
theorem codePolicy (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    Generic.CallPolicy ctx (n + 2) tcLevel (codeContract G ctx tcLevel) where
  node_zero := by
    intro first level numcells st hin
    obtain ⟨_, hin, hfuel⟩ := hin
    have hbc := hin.partition.bc
    change level ≤ bcount st.ptn level n at hbc
    have := bcount_le st.ptn level n
    omega
  node_step := by
    intro fuel hn first level numcells st hin cs bs fs hlen hc
    obtain ⟨rfl, hin, hfuel⟩ := hin
    subst level
    exact codes_node hn0 hgsz hsymm hloop hn cs bs fs numcells st hin hfuel hc
  sweep_none := by
    intro fuel cfuel first level numcells tc tv1 cell index st _ cs bs fs _ hc hphase
    have hn : st.compCanon ≤ 0 := by
      rcases hphase with hn | ⟨_, hp⟩
      · exact hn
      · cases hp
    exact ⟨bs, hc.returned hn, Generic.Grows.refl _⟩
  sweep_zero := by
    intro fuel first level numcells tc tv1 tv cell index st hin
    obtain ⟨hin, _, hcursor⟩ := hin
    have hb := hcursor tv rfl
    have := VSet.mem_lt (hin.cursor_mem tv rfl)
    omega
  sweep_step := by
    intro fuel cfuel hd hn first level numcells tc tv1 tv cell index st hin cs bs fs hlen hc hphase
    obtain ⟨hin, hfuel, hcursor⟩ := hin
    exact codes_sweep hn0 hgsz hsymm hloop hd hn first level numcells tc tv1 tv index cell st
      hin hfuel (hcursor tv rfl) cs bs fs hlen hc hphase

/-- An actual off-path node returns recoverable comparisons and a
monotone incumbent, retaining its incoming code path through every exit. -/
theorem node_codes {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells : Nat}
    {st : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hin : NodePre G ctx tcLevel level numcells st) (hfuel : n + 1 ≤ level + fuel)
    {cs bs fs : List Nat} (hlen : cs.length + 1 = level) (hc : Comparison ctx cs bs fs st) :
    let result := node false ctx (n + 2) tcLevel fuel level numcells st
    ∃ bs', ReturnCodes ctx cs bs' fs result.2 ∧ Generic.Grows (st.key ctx bs) (result.2.key ctx bs') := by
  rw [node_eq_generic]
  exact Generic.node_calls (codePolicy G ctx tcLevel hn0 hgsz hsymm hloop)
    false fuel level numcells st ⟨rfl, hin, hfuel⟩ cs bs fs hlen hc

/-- An actual later-sibling sweep transports settled comparisons across
nonlocal returns and composes incumbent growth across its visited children. -/
theorem sweep_codes {G : Colored n k} {ctx : Ctx n} {first : Bool}
    {tcLevel fuel cfuel level numcells tc tv1 index : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hin : SweepPre G ctx tcLevel first level numcells tc tv1 cursor cell st)
    (hfuel : n ≤ level + fuel) (hcursor : Generic.CursorFuel n cfuel cursor)
    {cs bs fs : List Nat} (hlen : cs.length = level) (hc : Comparison ctx cs bs fs st)
    (hphase : st.compCanon ≤ 0 ∨ first = false ∧ cursor.isSome) :
    let result := sweep first ctx (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
    ∃ bs', ReturnCodes ctx cs bs' fs result.2.2 ∧ Generic.Grows (st.key ctx bs) (result.2.2.key ctx bs') := by
  rw [sweep_eq_generic]
  exact Generic.sweep_calls (codePolicy G ctx tcLevel hn0 hgsz hsymm hloop)
    first fuel cfuel level numcells tc tv1 cursor cell index st ⟨hin, hfuel, hcursor⟩ cs bs fs hlen hc hphase

end Hex.GraphIso.Nauty.Engine
