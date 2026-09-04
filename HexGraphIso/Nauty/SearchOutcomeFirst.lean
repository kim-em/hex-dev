/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeInduction
public import HexGraphIso.Nauty.RootEquitable

public section

/-!
The pre-incumbent phase of the outcome-indexed search induction.

Before `firstterminal` installs the first leaf, the comparison, leaf, and
guide ledgers do not yet exist.  `FirstInv` records exactly the state that
the unique first descent must preserve.  The ordinary `RunInv` takes over
at the discrete leaf.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- State carried by the unique descent before the first leaf exists. -/
structure FirstInv (G : Colored n k) (ctx : Ctx) (level : Nat)
    (cs : List Nat) (numcells : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  searchOk : SearchOk G level numcells st
  codes : DescentCodes n cs st
  cheap : CheapOk ctx (initialPartition G).1
    (initPtn n (n + 2) (initialPartition G).2) level st
  cert : CertInv ctx level
    { lab := st.lab, ptn := st.ptn, active := st.active,
      numcells := numcells, hint := 0, maxpos := 0,
      longcode := numcells }
  trailOk : TrailOk ctx level st trail
  genEmpty : st.genTrace = #[]
  autosEmpty : st.autos = #[]
  canongSize : st.canong.size = ctx.n
  orbitId : ∀ v, v < ctx.n → st.orbits[v]! = v

/-- A nonempty root starts the first descent with empty stores, identity
orbits, and no active ancestor frame. -/
theorem FirstInv.root {G : Colored n k} (hn0 : 0 < n) :
    FirstInv G { n := n, g := rowsOf G } 1 []
      (initialPartition G).2.length
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      FrameTrail.empty := by
  have hok := root_searchOk G hn0
  refine ⟨hok, DescentCodes.root _ _ hn0, ?_, ?_,
    TrailOk.empty _ _ _, ?_, ?_, ?_, ?_⟩
  · exact CheapOk.root rfl hn0 hok (by simp [rootSt])
  · simpa only [rootSt] using certInv_initial G hn0
  · simp [rootSt]
  · simp [rootSt]
  · simp [rootSt]
  · intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]

/-- Reaching a discrete node installs the first leaf and enters the stable
post-incumbent invariant. -/
theorem FirstInv.terminal {G : Colored n k} {ctx : Ctx}
    {tcLevel level numcells : Nat} {cs : List Nat} {st : SearchSt}
    {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    RunInv G ctx tcLevel level full full full rs.numcells
      (firstterminal level (firstLeafSt ctx level numcells st))
      (some (pathLeafKey ctx full rs.lab)) trail := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let leaf := firstLeafSt ctx level numcells st
  let full := cs ++ [rs.longcode]
  have hlevelOne : 1 ≤ level := by omega
  have hok : SearchOk G level rs.numcells leaf := by
    apply refine_searchOk hn hn0 h.searchOk hlevelOne
    · rfl
    · rfl
    · exact Or.inl rfl
  have hfullLen : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hfullBound : full.length ≤ n := by
    rw [← hfullLen]
    rw [hlevel]
    exact h.codes.bound
  have hfullCodes : ∀ i, 1 ≤ i → i ≤ full.length →
      leaf.firstcode[i]! = full[i - 1]! := by
    simpa only [leaf, full, rs] using
      (firstLeafSt_codes (ctx := ctx) (nn := n) (level := level)
        (numcells := numcells) (cs := cs) (st := st) hlevel
        h.codes.firstSize (by omega) h.codes.content)
  have hfullLt : ∀ c ∈ full, c < codeSentinel := by
    intro c hc
    change c ∈ cs ++ [rs.longcode] at hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact h.codes.lt c hc
    · rw [List.mem_singleton.mp hc]
      exact refine_longcode_lt ctx level st.lab st.ptn st.active numcells
  have hcheap : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) level leaf := by
    apply h.cheap.refine hlevelOne <;> rfl
  have htrail : TrailOk ctx level leaf trail := by
    apply h.trailOk.refine
    · rw [h.searchOk.labSize, ← hn]
    · rw [h.searchOk.ptnSize, ← hn]
    · exact searchOk_end hn0 h.searchOk hlevelOne
    · rfl
    · rfl
  have hcheap' : CheapOk ctx (initialPartition G).1
      (initPtn n (n + 2) (initialPartition G).2) full.length leaf := by
    rw [← hfullLen]
    exact hcheap
  apply RunInv.firstterminal (hpath := hfullLen)
      (hok := hok) (hbound := hfullBound) (hcodes := hfullCodes)
      (hlt := hfullLt) (hcheap := hcheap') (htrail := htrail)
  · simp [leaf, firstLeafSt, h.codes.firstSize]
  · simp [leaf, firstLeafSt, h.codes.canonSize]
  · simpa [leaf, firstLeafSt] using h.canongSize
  · simpa [leaf, firstLeafSt] using h.genEmpty
  · simpa [leaf, firstLeafSt] using h.autosEmpty
  · intro he
    have := congrArg List.length he
    simp [full] at this

/-- A discrete node on the first descent returns an exact located receipt
and the stable state installed by that leaf. -/
theorem FirstInv.terminalReceipt {G : Colored n k} {ctx : Ctx}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt} {trail : FrameTrail}
    (hn : ctx.n = n) (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeReceipt trail ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
        out.2 numcells none (some (pathLeafKey ctx full rs.lab)) out.1 ∧
      RunInv G ctx tcLevel level full full full rs.numcells out.2
        (some (pathLeafKey ctx full rs.lab)) trail := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := cs ++ [rs.longcode]
  let leaf := firstLeafSt ctx level numcells st
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hrun : RunInv G ctx tcLevel level full full full rs.numcells
      (firstterminal level leaf) (some (pathLeafKey ctx full rs.lab))
      trail := by
    simpa only [rs, full, leaf] using h.terminal hn hn0 hlevel
  have hdisc : discreteAt rs.ptn level ctx.n = true := by
    rw [← refine_discrete_iff hn hn0 h.searchOk (by omega)]
    exact hnum
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full rs.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  constructor
  · rw [hstate]
    apply NodeReceipt.complete
    · apply NodeSound.ofExact
      simp only [incMax, hnode, rs, full]
    · rfl
    · apply canonlevel_ne_zero_of_stInc
      simpa only [leaf] using hrun.read
    · simpa only [leaf] using hrun.read
    · simp only [incMax, hnode, rs, full]
  · rw [hstate]
    exact hrun

end Hex.GraphIso.Nauty
