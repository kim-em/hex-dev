/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcome
import all HexGraphIso.Nauty.Search

public section

/-!
Base cases of the outcome-indexed search induction.

These lemmas keep node fuel and child-loop fuel visibly separate.  In
particular, loop-fuel exhaustion is represented by `LoopResult.exhausted`,
whereas reaching the end cursor with positive fuel is a genuine completed
sweep.
-/

namespace Hex.GraphIso.Nauty

/-! # First-path leaf seed -/

/-- Once the first descent reaches a real leaf, `firstterminal` installs
exactly that leaf as the semantic incumbent. -/
theorem stInc_firstterminal {ctx : Ctx} {nn level : Nat} {cs : List Nat}
    {st : SearchSt}
    (hlevel : level = cs.length) (hne : cs ≠ [])
    (hcanon : st.canoncode.size = nn + 2)
    (hbound : cs.length ≤ nn)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel) :
    stInc ctx (firstterminal level st) =
      some (pathLeafKey ctx cs st.lab) := by
  subst level
  have hinv := firstterminal_codeInv hcanon hbound hcodes hlt
  have hcomp : (firstterminal cs.length st).compCanon ≠ 1 := by
    rw [firstterminal]
    simp only [Id.run_bind, Id.run_pure]
    omega
  rw [stInc_eq_ghost hinv hcomp]
  simp only [ghostInc, hne, ↓reduceIte]
  rfl

/-- The state immediately before the first-path leaf is installed. -/
@[expose] def firstLeafSt (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) : SearchSt :=
  let rs := refine ctx level st.lab st.ptn st.active numcells
  { st with
    lab := rs.lab
    ptn := rs.ptn
    active := rs.active
    firstcode := st.firstcode.set! level rs.longcode
    firsttc := st.firsttc.set! level (-1)
    numnodes := st.numnodes + 1 }

/-- The discrete arm of `firstPathNode` is exactly `firstterminal` on the
refined leaf state. -/
theorem firstPath_discrete_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hdisc : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    firstPathNode ctx inf tcLevel (fuel + 1) level numcells st =
      (Int.ofNat level - 1, firstterminal level
        (firstLeafSt ctx level numcells st)) := by
  rw [firstPathNode]
  simp only [Id.run_pure, hdisc, ne_eq,
    not_true_eq_false, ite_false,
    beq_self_eq_true, ite_true, firstLeafSt]

/-- Writing the current refinement code extends the stored first-path
code sequence by one entry. -/
theorem firstLeafSt_codes {ctx : Ctx} {nn level numcells : Nat}
    {cs : List Nat} {st : SearchSt}
    (hlevel : level = cs.length + 1)
    (hsize : st.firstcode.size = nn + 2) (hle : level ≤ nn)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!) :
    ∀ i, 1 ≤ i → i ≤ (cs ++ [(refine ctx level st.lab st.ptn
      st.active numcells).longcode]).length →
      (firstLeafSt ctx level numcells st).firstcode[i]! =
        (cs ++ [(refine ctx level st.lab st.ptn st.active
          numcells).longcode])[i - 1]! := by
  intro i hi hbound
  rcases Decidable.em (i = level) with rfl | hne
  · change (st.firstcode.set! i (refine ctx i st.lab st.ptn
        st.active numcells).longcode)[i]! = _
    rw [Array.getElem!_set!_self _ _ _ (by
      rw [hsize]
      omega)]
    have hi1 : i - 1 = cs.length := by omega
    rw [hi1]
    rw [getElem!_append_right'' (Nat.le_refl _) (by
      simp only [List.length_singleton]
      omega)]
    simp only [Nat.sub_self]
    rfl
  · change (st.firstcode.set! level (refine ctx level st.lab st.ptn
        st.active numcells).longcode)[i]! = _
    rw [Array.getElem!_set!_ne _ _ _ _ (fun h => hne h.symm)]
    have hlen : (cs ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]).length = cs.length + 1 := by simp
    have hics : i ≤ cs.length := by
      rw [hlen] at hbound
      omega
    rw [getElem!_append_left'' (by omega)]
    exact hcodes i hi hics

/-- A discrete first-path node installs the exact specification leaf and
returns ordinary completion.  This is the phase transition from an absent
incumbent to the stable off-path comparison state. -/
theorem firstPath_discrete {ctx : Ctx} {nn inf tcLevel specFuel fuel
    level numcells : Nat} {cs : List Nat} {st : SearchSt}
    (hlevel : level = cs.length + 1)
    (hfirstSize : st.firstcode.size = nn + 2)
    (hcanonSize : st.canoncode.size = nn + 2) (hle : level ≤ nn)
    (hcodes : ∀ i, 1 ≤ i → i ≤ cs.length →
      st.firstcode[i]! = cs[i - 1]!)
    (hlt : ∀ c ∈ cs, c < codeSentinel)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true) :
    NodeResult ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells none
      (some (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells))
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
  let code := (refine ctx level st.lab st.ptn st.active numcells).longcode
  let full := cs ++ [code]
  let leaf := firstLeafSt ctx level numcells st
  have hfullLen : full.length = level := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hfullNe : full ≠ [] := by
    intro he
    have := congrArg List.length he
    simp only [full, List.length_append, List.length_singleton,
      List.length_nil] at this
    omega
  have hfullBound : full.length ≤ nn := by omega
  have hfullCodes : ∀ i, 1 ≤ i → i ≤ full.length →
      leaf.firstcode[i]! = full[i - 1]! := by
    simpa only [leaf, full, code] using
      (firstLeafSt_codes (ctx := ctx) (nn := nn) (level := level)
        (numcells := numcells) (cs := cs) (st := st) hlevel
        hfirstSize hle hcodes)
  have hfullLt : ∀ c ∈ full, c < codeSentinel := by
    intro c hc
    change c ∈ cs ++ [code] at hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hlt c hc
    · simp only [List.mem_singleton] at hc
      subst c
      exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  have hread : stInc ctx (firstterminal level leaf) =
      some (pathLeafKey ctx full
        (refine ctx level st.lab st.ptn st.active numcells).lab) := by
    have h := stInc_firstterminal (ctx := ctx) (nn := nn)
      (level := level) (cs := full) (st := leaf) hfullLen.symm hfullNe
      (by simpa only [leaf, firstLeafSt] using hcanonSize)
      hfullBound hfullCodes hfullLt
    simpa only [leaf, firstLeafSt] using h
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full
        (refine ctx level st.lab st.ptn st.active numcells).lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  apply NodeResult.complete
  · exact NodeSound.ofExact rfl
  · rfl
  · rw [firstterminal]
    simp only [Id.run_bind, Id.run_pure]
    omega
  · rwa [hnode]
  · rfl

/-- A first-path node with no runtime fuel reports exhaustion. -/
theorem firstPath_zero (ctx : Ctx) (inf tcLevel specFuel level numcells : Nat)
    (cs : List Nat) (st : SearchSt) (best : Option Key) :
    NodeResult ctx tcLevel specFuel 0 level cs st
      (firstPathNode ctx inf tcLevel 0 level numcells st).2 numcells
      best best
      (firstPathNode ctx inf tcLevel 0 level numcells st).1 := by
  rw [firstPathNode]
  exact .exhausted rfl rfl rfl rfl

/-- An off-path node with no runtime fuel reports exhaustion. -/
theorem otherNode_zero (ctx : Ctx) (inf tcLevel specFuel level numcells : Nat)
    (cs : List Nat) (st : SearchSt) (best : Option Key) :
    NodeResult ctx tcLevel specFuel 0 level cs st
      (otherNode ctx inf tcLevel 0 level numcells st).2 numcells
      best best
      (otherNode ctx inf tcLevel 0 level numcells st).1 := by
  rw [otherNode]
  exact .exhausted rfl rfl rfl rfl

/-- First-path child-loop fuel exhaustion is not completion. -/
theorem firstLoop_zero (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell index : Nat) (bound : Key)
    (st : SearchSt) (best : Option Key)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopResult ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn tc len
      numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell index st).1 := by
  rw [firstChildLoop]
  exact .exhausted rfl (.refl ctx bound best) tcell cursor hcover
    (by omega) hcursor

/-- Off-path child-loop fuel exhaustion is not completion. -/
theorem otherLoop_zero (ctx : Ctx)
    (inf tcLevel specFuel runFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tv? cursor : Option Nat) (tcell : Nat) (bound : Key) (st : SearchSt)
    (best : Option Key)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hcursor : ∀ v, cursor = some v → v < ctx.n) :
    LoopResult ctx tcLevel specFuel runFuel 0 level cs rsLab rsPtn tc len
      numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).2
      best best
      (otherChildLoop ctx inf tcLevel runFuel 0 level numcells tc tv1 tv?
        tcell st).1 := by
  rw [otherChildLoop]
  exact .exhausted rfl (.refl ctx bound best) tcell cursor hcover
    (by omega) hcursor

/-- With positive loop fuel, an absent next child completes the first-path
sweep rather than exhausting it. -/
theorem firstLoop_done (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len : Nat)
    (tcell index : Nat) (cursor : Option Nat) (bound : Key)
    (st : SearchSt) (best : Option Key)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = none) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell index st).1 := by
  rw [firstChildLoop]
  case x_1 => omega
  exact .complete rfl (.refl ctx bound best) tcell cursor hcover fun o ho =>
    no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- With positive loop fuel, an absent next child completes the off-path
sweep rather than exhausting it. -/
theorem otherLoop_done (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best : Option Key)
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = none) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).2
      best best
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 none tcell st).1 := by
  rw [otherChildLoop]
  case x_1 => omega
  exact .complete rfl (.refl ctx bound best) tcell cursor hcover fun o ho =>
    no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- A non-root orbit pointer skips the current first-path child and
continues with ranked coverage advanced past that child. -/
theorem firstLoop_orbitSkip (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 tv : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell index o : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best : Option Key)
    (gens : List (Array Nat))
    (hcover : SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len
      numcells tcell cursor best)
    (hnext : nextElem tcell cursor = some tv) (ho : o < len)
    (htv : rsLab[tc + o]! = tv)
    (hgsz : ctx.g.size = ctx.n)
    (hbg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hv : ∀ γ ∈ gens, checkAutom ctx.g γ ctx.n = true)
    (hstab : ∀ γ ∈ gens, CellStab rsPtn level rsLab γ)
    (hs : rsLab.size = ctx.n) (hinj : LabInj rsLab rsLab.size)
    (hok : LabOk rsLab ctx.n) (hsp : rsPtn.size = ctx.n)
    (hend : rsPtn[rsPtn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, rsPtn[q]! ≤ level ∨
      rsPtn[q]! = ctx.n + 2)
    (hic : IsCell rsPtn level tc len) (hrange : tc + len ≤ ctx.n)
    (hlf : level + 1 + specFuel ≤ ctx.n + 1)
    (hsound : OrbSound (OrbConn gens ctx.n) st.orbits ctx.n)
    (horbit : (st.orbits[tv]! == tv) = false)
    (hrec : ∀ index',
      SweepCover ctx tcLevel specFuel level cs rsLab rsPtn tc len numcells
        tcell (some tv) best →
      LoopResult ctx tcLevel specFuel runFuel loopFuel level cs rsLab rsPtn
        tc len numcells tcell (some tv) bound st
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' st).2.2
        best best
        (firstChildLoop ctx inf tcLevel runFuel loopFuel level numcells tc
          tv1 (nextElem tcell (some tv)) tcell index' st).1) :
    LoopResult ctx tcLevel specFuel runFuel (loopFuel + 1) level cs rsLab
      rsPtn tc len numcells tcell cursor bound st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).2.2
      best best
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level numcells
        tc tv1 (some tv) tcell index st).1 := by
  have hne : st.orbits[tv]! ≠ tv := by
    simpa only [beq_eq_false_iff_ne] using horbit
  have hcover' := hcover.orbitSkip hnext ho htv hgsz hbg hv hstab hs hinj
    hok hsp hend hvals hic hrange hlf hsound hne
  rw [firstChildLoop]
  simp only [horbit, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run]
  rcases hidx : (st.orbits[tv]! == tv1) with _ | _ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;>
    exact (hrec _ hcover').step (nextElem_after hnext)

end Hex.GraphIso.Nauty
