/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcome
public import HexGraphIso.Nauty.SearchReach
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

/-- Code storage on the unique descent before the first leaf exists.
Unlike `FirstCodeInv`, this phase has no stored first-leaf sentinel yet. -/
structure DescentCodes (nn : Nat) (cs : List Nat) (st : SearchSt) : Prop where
  firstSize : st.firstcode.size = nn + 2
  canonSize : st.canoncode.size = nn + 2
  bound : cs.length + 1 ≤ nn
  content : ∀ i, 1 ≤ i → i ≤ cs.length →
    st.firstcode[i]! = cs[i - 1]!
  lt : ∀ c ∈ cs, c < codeSentinel

/-- The nonempty root begins the pre-incumbent descent with no codes. -/
theorem DescentCodes.root {n : Nat} (lab : Array Nat)
    (cellEnds : List Nat) (hn0 : 0 < n) :
    DescentCodes n [] (rootSt n lab cellEnds) := by
  constructor
  · simp [rootSt]
  · simp [rootSt]
  · simp only [List.length_nil]
    omega
  · intro i _ hi
    simp only [List.length_nil] at hi
    omega
  · intro c hc
    cases hc

/-- Writing one real refinement code advances the pre-incumbent descent
to its child. -/
theorem DescentCodes.next {nn : Nat} {cs : List Nat} {st st' : SearchSt}
    {code : Nat} (h : DescentCodes nn cs st)
    (hfirst : st'.firstcode = st.firstcode.set! (cs.length + 1) code)
    (hcanon : st'.canoncode = st.canoncode)
    (hbound : cs.length + 2 ≤ nn) (hlt : code < codeSentinel) :
    DescentCodes nn (cs ++ [code]) st' := by
  constructor
  · rw [hfirst, Array.size_set!, h.firstSize]
  · rw [hcanon, h.canonSize]
  · simp only [List.length_append, List.length_singleton]
    exact hbound
  · intro i hi hlast
    rcases Decidable.em (i = cs.length + 1) with heq | hne
    · subst i
      rw [hfirst, Array.getElem!_set!_self _ _ _ (by
        rw [h.firstSize]
        omega)]
      have hi : cs.length + 1 - 1 = cs.length := by omega
      rw [hi, getElem!_append_right'' (Nat.le_refl _) (by simp)]
      simp only [Nat.sub_self]
      rfl
    · rw [hfirst, Array.getElem!_set!_ne _ _ _ _
          (fun he => hne he.symm)]
      have hics : i ≤ cs.length := by
        simp only [List.length_append, List.length_singleton] at hlast
        omega
      rw [getElem!_append_left'' (by omega)]
      exact h.content i hi hics
  · intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact h.lt c hc
    · rw [List.mem_singleton.mp hc]
      exact hlt

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

/-- Under the search invariant, the transcription's refined cell-count
guard agrees with the specification's discreteness guard. -/
theorem refine_discrete_iff {G : Colored n k} {ctx : Ctx}
    (hn : ctx.n = n) (hn0 : 0 < n) {level numcells : Nat}
    {st : SearchSt} (hok : SearchOk G level numcells st)
    (hlevel : 1 ≤ level) :
    (refine ctx level st.lab st.ptn st.active numcells).numcells =
        ctx.n ↔
      discreteAt (refine ctx level st.lab st.ptn st.active
        numcells).ptn level ctx.n = true := by
  subst n
  have hend := searchOk_end hn0 hok hlevel
  have hnn : ctx.n = st.ptn.size := by rw [hok.ptnSize]
  have hls : st.lab.size = st.ptn.size := by
    rw [hok.labSize, hok.ptnSize]
  have hnc := hok.count
  have hR := refine_refInv (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) (Nat.le_of_eq hnn) hls hend
  have hRend : (refine ctx level st.lab st.ptn st.active
      numcells).ptn[(refine ctx level st.lab st.ptn st.active
        numcells).ptn.size - 1]! ≤ level := by
    rw [hR.ptnSize, refine_frozen hnn hls hend hend]
    exact hend
  have hcount := refine_bcount (ctx := ctx) (level := level)
    (lab := st.lab) (ptn := st.ptn) (active := st.active)
    (numcells := numcells) hnn hls hend
  have haccurate : (refine ctx level st.lab st.ptn st.active
      numcells).numcells =
      bcount (refine ctx level st.lab st.ptn st.active
        numcells).ptn level ctx.n := by omega
  rw [haccurate]
  exact (discreteAt_iff_bcount (by rw [hR.ptnSize, ← hnn]) hRend).symm

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

/-- The invariant-packaged first-path leaf rule: the search invariant
supplies guard agreement and `DescentCodes` supplies the pre-incumbent
code store. -/
theorem firstPath_discrete_of_ok {G : Colored n k} {ctx : Ctx}
    (hn : ctx.n = n) (hn0 : 0 < n) {inf tcLevel specFuel fuel
      numcells : Nat} {cs : List Nat} {st : SearchSt}
    (hok : SearchOk G (cs.length + 1) numcells st)
    (hcodes : DescentCodes n cs st)
    (hnum : (refine ctx (cs.length + 1) st.lab st.ptn st.active
      numcells).numcells = ctx.n) :
    NodeResult ctx tcLevel (specFuel + 1) (fuel + 1) (cs.length + 1) cs st
      (firstPathNode ctx inf tcLevel (fuel + 1) (cs.length + 1)
        numcells st).2 numcells none
      (some (nodeKey ctx tcLevel (specFuel + 1) (cs.length + 1) cs st
        numcells))
      (firstPathNode ctx inf tcLevel (fuel + 1) (cs.length + 1)
        numcells st).1 := by
  apply firstPath_discrete (nn := n) (hlevel := rfl)
    hcodes.firstSize hcodes.canonSize hcodes.bound hcodes.content
    hcodes.lt hnum
  exact (refine_discrete_iff hn hn0 hok (by omega)).mp hnum

/-- The root outcome is closed outright when root refinement is already
discrete. -/
theorem root_result_of_discrete {G : Colored n k} (hn0 : 0 < n)
    (hnum : (refine { n := n, g := rowsOf G } 1
      (rootSt n (initialPartition G).1 (initialPartition G).2).lab
      (rootSt n (initialPartition G).1 (initialPartition G).2).ptn
      (rootSt n (initialPartition G).1 (initialPartition G).2).active
      (initialPartition G).2.length).numcells = n) :
    NodeResult { n := n, g := rowsOf G } 100 n (n + 2) 1 []
      (rootSt n (initialPartition G).1 (initialPartition G).2)
      (rootOut n (rowsOf G) (initialPartition G).1
        (initialPartition G).2)
      (initialPartition G).2.length none
      (some (nodeKey { n := n, g := rowsOf G } 100 n 1 []
        (rootSt n (initialPartition G).1 (initialPartition G).2)
        (initialPartition G).2.length))
      (firstPathNode { n := n, g := rowsOf G } (n + 2) 100 (n + 2) 1
        (initialPartition G).2.length
        (rootSt n (initialPartition G).1 (initialPartition G).2)).1 := by
  have h := firstPath_discrete_of_ok (G := G)
    (ctx := { n := n, g := rowsOf G }) rfl hn0
    (inf := n + 2) (tcLevel := 100) (specFuel := n - 1)
    (fuel := n + 1) (cs := [])
    (st := rootSt n (initialPartition G).1 (initialPartition G).2)
    (root_searchOk G hn0)
    (DescentCodes.root _ _ hn0) hnum
  simpa only [List.length_nil, Nat.zero_add, Nat.sub_add_cancel
    (by omega : 1 ≤ n), rootOut] using h

/-! # Off-path leaf incumbent -/

/-- The refined and compared state on entry to an off-path leaf event. -/
@[expose] def otherLeafSt (ctx : Ctx) (level numcells : Nat)
    (st : SearchSt) : SearchSt :=
  let rs := refine ctx level st.lab st.ptn st.active numcells
  otherNodePrep level rs.longcode
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }

/-- If a discrete off-path leaf requests an early unwind, `otherNode`
returns its `processnode` result verbatim. -/
theorem otherNode_leaf_early (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      processnode ctx level ctx.n (otherLeafSt ctx level numcells st) := by
  unfold otherLeafSt at hearly ⊢
  rw [otherNode]
  simp only [hnum]
  rw [ite_eq_right (by omega), ite_eq_left hearly]
  rfl

/-- The comparison-blind cleanup performed when a leaf event does not
request an early unwind. -/
@[expose] def leafFinish (ctx : Ctx) (level : Nat)
    (st : SearchSt) : SearchSt :=
  let st := if st.needshortprune then
      { st with needshortprune := false }
    else st
  if ¬ cheapautom st.ptn level ctx.n then
    { st with noncheaplevel := level + 1 }
  else st

/-- A discrete off-path leaf that does not unwind runs the empty child
sweep and returns ordinary node completion. -/
theorem otherNode_leaf_done_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)) :
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      (Int.ofNat level - 1, leafFinish ctx level
        (processnode ctx level ctx.n
          (otherLeafSt ctx level numcells st)).2) := by
  unfold otherLeafSt at hdone ⊢
  rw [otherNode]
  simp only [hnum]
  rw [ite_eq_right (by omega), ite_eq_right hdone]
  have hzsub : ∀ st' : SearchSt, shortprune 0 st' = 0 := by
    intro st'
    rw [shortprune]
    rcases hb : st'.autos.back? with _ | pair
    · rfl
    · exact Nat.zero_and pair.2
  generalize hPR : (processnode ctx level ctx.n
    (otherNodePrep level (refine ctx level st.lab st.ptn st.active
      numcells).longcode
      { st with
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
        active := (refine ctx level st.lab st.ptn st.active numcells).active
        numnodes := st.numnodes + 1 })).2 = PR
  rcases hshort : PR.needshortprune with _ | _
  · simp only [hshort, Bool.false_eq_true, ite_false, leafFinish]
    rcases hcheap : cheapautom PR.ptn level ctx.n with _ | _
    · simp only [Bool.false_eq_true, not_false_eq_true,
        ite_true, nextElem, Int.reduceToNat,
        otherChildLoop, Id.run_pure]
    · simp only [not_true_eq_false, ite_false, ite_true, nextElem,
        Int.reduceToNat, otherChildLoop, Id.run_pure]
  · simp only [hshort, ite_true, hzsub, leafFinish]
    rcases hcheap : cheapautom PR.ptn level ctx.n with _ | _
    · simp only [Bool.false_eq_true, not_false_eq_true,
        ite_true, nextElem, Int.reduceToNat,
        otherChildLoop, Id.run_pure]
    · simp only [not_true_eq_false, ite_false, ite_true, nextElem,
        Int.reduceToNat, otherChildLoop, Id.run_pure]

/-- The maximum of two installed leaf keys still has a nonempty path. -/
theorem incKey_max_nonempty {ctx : Ctx} {bs cs bs' : List Nat}
    {canonlab canonlab' lab : Array Nat} (hbs : bs ≠ [])
    (hcs : cs ≠ []) (hmax : incKey ctx bs' canonlab' =
      keyMax (incKey ctx bs canonlab) (pathLeafKey ctx cs lab)) :
    bs' ≠ [] := by
  intro he
  subst bs'
  rcases keyMax_mem (incKey ctx bs canonlab)
      (pathLeafKey ctx cs lab) with hk | hk
  · rw [hk] at hmax
    have hc := congrArg Key.codes hmax
    simp only [incKey] at hc
    have hl := congrArg List.length hc
    simp only [List.length_append, List.length_singleton,
      List.length_nil] at hl
    exact hbs (List.length_eq_zero_iff.mp (by omega))
  · rw [hk] at hmax
    have hc := congrArg Key.codes hmax
    simp only [incKey, pathLeafKey] at hc
    have hl := congrArg List.length hc
    simp only [List.length_append, List.length_singleton,
      List.length_nil] at hl
    exact hcs (List.length_eq_zero_iff.mp (by omega))

/-- The faithful off-path leaf event can be read through `stInc` even in
the row-rejection arm, where `compCanon` is deliberately reused as a row
comparison result. -/
theorem processnode_leaf_read {nn : Nat} {ctx : Ctx}
    {cs bs : List Nat} {numcells : Nat} {st : SearchSt}
    (hcinv : CodeCmpInv nn cs bs st.canoncode st.canonlevel
      st.eqlevCanon st.compCanon)
    (hginv : CanongInv ctx st.canong st.canonlab st.samerows)
    (hcsn : cs.length ≤ nn) (hbs : bs ≠ []) (hcs : cs ≠ [])
    (hef : ¬((st.eqlevFirst == cs.length) = true))
    (hnc : (numcells == ctx.n) = true) :
    ∃ bs' : List Nat,
      stInc ctx (processnode ctx cs.length numcells st).2 =
        some (keyMax (incKey ctx bs st.canonlab)
          (pathLeafKey ctx cs st.lab)) ∧
      CanongInv ctx (processnode ctx cs.length numcells st).2.canong
        (processnode ctx cs.length numcells st).2.canonlab
        (processnode ctx cs.length numcells st).2.samerows ∧
      (((processnode ctx cs.length numcells st).2.compCanon ≤ 0 ∧
        CodeCmpInv nn cs bs'
          (processnode ctx cs.length numcells st).2.canoncode
          (processnode ctx cs.length numcells st).2.canonlevel
          (processnode ctx cs.length numcells st).2.eqlevCanon
          (processnode ctx cs.length numcells st).2.compCanon) ∨
        ((processnode ctx cs.length numcells st).2.compCanon < 0 ∧
          CodeCmpInv nn cs bs'
            (processnode ctx cs.length numcells st).2.canoncode
            (processnode ctx cs.length numcells st).2.canonlevel
            (processnode ctx cs.length numcells st).2.eqlevCanon 0)) ∧
      ((processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel st.eqlevCanon ∨
        (processnode ctx cs.length numcells st).1 =
          pruneReturn st.noncheaplevel st.allsamelevel
            (Int.ofNat cs.length) ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaFirst ∨
        (processnode ctx cs.length numcells st).1 =
          Int.ofNat st.gcaCanon) := by
  obtain ⟨bs', hmax, hcanong, hcmp, hreturn⟩ :=
    processnode_leaf hcinv hginv hcsn hef hnc
  have hbs' := incKey_max_nonempty hbs hcs hmax
  have hread : stInc ctx (processnode ctx cs.length numcells st).2 =
      some (incKey ctx bs'
        (processnode ctx cs.length numcells st).2.canonlab) := by
    rcases hcmp with hcmp | hcmp
    · rw [stInc_eq_ghost hcmp.2 (by omega)]
      simp only [ghostInc, hbs', ↓reduceIte]
    · rw [stInc_eq_ghost hcmp.2 (by omega)]
      simp only [ghostInc, hbs', ↓reduceIte]
  refine ⟨bs', ?_, hcanong, hcmp, hreturn⟩
  rw [hread, hmax]

/-- Reading a present incumbent proves that a canonical leaf has been
installed in the mutable state. -/
theorem canonlevel_ne_zero_of_stInc {ctx : Ctx} {st : SearchSt} {B : Key}
    (h : stInc ctx st = some B) : st.canonlevel ≠ 0 := by
  intro hz
  rw [stInc, ite_eq_left hz] at h
  cases h

/-- An early non-first-path leaf return has already absorbed its whole
(singleton) specification subtree.  Its signed comparison return is a
local prune outcome; generator returns can subsequently be strengthened to
`unwind` by the carrier/guide layer. -/
theorem otherNode_leaf_pruned {ctx : Ctx} {nn inf tcLevel specFuel fuel
    level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hlevel : level = cs.length + 1) (hlevelN : level ≤ nn)
    (hbs : bs ≠ [])
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hcinv : CodeCmpInv nn
      (cs ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs
      (otherLeafSt ctx level numcells st).canoncode
      (otherLeafSt ctx level numcells st).canonlevel
      (otherLeafSt ctx level numcells st).eqlevCanon
      (otherLeafSt ctx level numcells st).compCanon)
    (hginv : CanongInv ctx (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hearly : (processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level) :
    NodeResult ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells (some (incKey ctx bs st.canonlab))
      (some (keyMax (incKey ctx bs st.canonlab)
        (pathLeafKey ctx
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab)))
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  rw [otherNode_leaf_early ctx inf tcLevel fuel level numcells st hnum
    hearly]
  let code := (refine ctx level st.lab st.ptn st.active numcells).longcode
  let full := cs ++ [code]
  let pre : SearchSt :=
    { st with
      lab := (refine ctx level st.lab st.ptn st.active numcells).lab
      ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
      active := (refine ctx level st.lab st.ptn st.active numcells).active
      numnodes := st.numnodes + 1 }
  let leaf := otherLeafSt ctx level numcells st
  have hfullLen : full.length = level := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hfullNe : full ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [full, List.length_append, List.length_singleton,
      List.length_nil] at hl
    omega
  have hleaf := processnode_leaf_read (ctx := ctx) (nn := nn)
    (cs := full) (bs := bs) (numcells := ctx.n) (st := leaf)
    (by simpa only [full, code, leaf] using hcinv) hginv
    (by rw [hfullLen]; exact hlevelN) hbs hfullNe
    (by simpa only [hfullLen, leaf] using hef) (by simp)
  obtain ⟨bs', hread, _, _, _⟩ := hleaf
  have hframes := otherNodePrep_frames level code pre
  rcases hframes with
    ⟨hcanon, _, _, _, _, _, _, _, _, _, _, hlab, _⟩
  have hleafCanon : leaf.canonlab = st.canonlab := by
    change (otherNodePrep level code pre).canonlab = st.canonlab
    rw [hcanon]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    change (otherNodePrep level code pre).lab = _
    rw [hlab]
  rw [hfullLen, hleafCanon, hleafLab] at hread
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full
        (refine ctx level st.lab st.ptn st.active numcells).lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  apply NodeResult.pruned (target :=
    (processnode ctx level ctx.n leaf).1)
  · apply NodeSound.ofExact
    rw [incMax, hnode]
  · rfl
  · exact hearly
  · exact canonlevel_ne_zero_of_stInc hread
  · simpa only [leaf] using hread
  · rw [incMax, hnode]

/-- Leaf cleanup changes no field used to read the incumbent. -/
theorem stInc_leafFinish (ctx : Ctx) (level : Nat) (st : SearchSt) :
    stInc ctx (leafFinish ctx level st) = stInc ctx st := by
  rw [leafFinish]
  split <;> split <;> rfl

/-- The sole state adjustment after a completed first-path child sweep. -/
@[expose] def firstFinish (level tcellsize index : Nat)
    (st : SearchSt) : SearchSt :=
  if tcellsize == index ∧ st.allsamelevel == level + 1 then
    { st with allsamelevel := st.allsamelevel - 1 }
  else st

/-- First-path sweep cleanup does not alter the installed incumbent. -/
theorem stInc_firstFinish (ctx : Ctx) (level tcellsize index : Nat)
    (st : SearchSt) :
    stInc ctx (firstFinish level tcellsize index st) = stInc ctx st := by
  rw [firstFinish]
  split <;> rfl

/-- First-path sweep cleanup does not uninstall an incumbent. -/
theorem canonlevel_firstFinish (level tcellsize index : Nat)
    (st : SearchSt) :
    (firstFinish level tcellsize index st).canonlevel = st.canonlevel := by
  rw [firstFinish]
  split <;> rfl

/-- A generator payload is insensitive to the first-path exit counter. -/
theorem Unwind.firstFinish {ctx : Ctx} {tcLevel target level size index : Nat}
    {st : SearchSt} {best : Option Key}
    (h : Unwind ctx tcLevel target st best) :
    Unwind ctx tcLevel target (firstFinish level size index st) best := by
  cases h with
  | first anchor carrier =>
      apply Unwind.first anchor
      rw [Nauty.firstFinish]
      split <;> exact carrier
  | canon anchor carrier =>
      apply Unwind.canon anchor
      rw [Nauty.firstFinish]
      split <;> exact carrier

/-- Every node outcome crosses the first-path exit counter update. -/
theorem NodeResult.firstFinish {ctx : Ctx}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs : List Nat} {st out : SearchSt} {best outBest : Option Key}
    {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeResult ctx tcLevel specFuel runFuel level cs st out numcells
      best outBest r) :
    NodeResult ctx tcLevel specFuel runFuel level cs st
      (firstFinish level size index out) numcells best outBest r := by
  cases h with
  | complete sound returned installed read full =>
      exact .complete sound returned
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | unwind sound target returned below payload =>
      exact .unwind sound target returned below payload.firstFinish
  | pruned sound target returned below installed read full =>
      exact .pruned sound target returned below
        (by rw [canonlevel_firstFinish]; exact installed)
        ((stInc_firstFinish ctx level size index out).trans read) full
  | exhausted empty returned unchanged bestUnchanged =>
      exact (hfuel empty).elim

/-- A non-discrete first-path node is its explicit prefix state, one child
loop, and the single exit-counter update. -/
theorem firstPath_internal_state (ctx : Ctx)
    (inf tcLevel fuel level numcells : Nat) (st : SearchSt)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
    let pre0 : SearchSt := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      rs.numcells mt.1 ((nextElem mt.2.1 none).getD 0)
      (nextElem mt.2.1 none) mt.2.1 0 pre
    firstPathNode ctx inf tcLevel (fuel + 1) level numcells st =
      match L.1 with
      | some r => (r, L.2.2)
      | none => (Int.ofNat level - 1,
          firstFinish level mt.2.2 L.2.1 L.2.2) := by
  rw [firstPathNode]
  simp only [hnum, ne_eq, not_false_eq_true, ite_true,
    beq_eq_false_iff_ne.mpr hnum, Bool.false_eq_true, ite_false,
    Int.ofNat_eq_natCast, Int.toNat_natCast]
  split <;>
    generalize hL : firstChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _ _ = L <;>
    rcases L with ⟨r, index, out⟩ <;>
    cases r <;> simp only [Id.run_pure, firstFinish] <;>
    repeat' split <;> rfl

set_option maxHeartbeats 800000 in
/-- A sound child-loop result supplies the complete outcome of a
non-discrete first-path node.  The theorem keeps the node's runtime fuel,
the recursive node fuel, and the loop fuel separate. -/
theorem firstPath_internal_of_loop (ctx : Ctx)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs : List Nat) (st : SearchSt) (best outBest : Option Key)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ ctx.n)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      let rs := refine ctx level st.lab st.ptn st.active numcells
      let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      keysMax
        (sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
          rs.lab rs.ptn mt.1 rs.numcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level (cs ++ [rs.longcode])
            rs.lab rs.ptn mt.1 rs.numcells (o + 1)))
    (hlen : (maketargetcell ctx
      (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn level
      tcLevel (-1)).2.2 = tail + 1) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
    let pre0 : SearchSt := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level ctx.n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (ctx.n + 1) level
      rs.numcells mt.1 ((nextElem mt.2.1 none).getD 0)
      (nextElem mt.2.1 none) mt.2.1 0 pre
    LoopResult ctx tcLevel specFuel fuel (ctx.n + 1) level
      (cs ++ [rs.longcode]) rs.lab rs.ptn mt.1 mt.2.2 rs.numcells
      mt.2.1 none
      (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells)
      pre L.2.2 best outBest L.1 →
    NodeResult ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  dsimp only
  intro hloop
  rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
  generalize hL : firstChildLoop ctx inf tcLevel fuel (ctx.n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := NodeResult.of_loop_none (ctx := ctx)
        (nodeRunFuel := fuel + 1)
        (cursor := none) (loopFuel := ctx.n + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega) hloop
      exact hnode.firstFinish (by omega)
  | some r =>
      exact NodeResult.of_loop_some (ctx := ctx) (nodeRunFuel := fuel + 1)
        rfl hloop

/-- The complementary off-path leaf case completes after its empty child
sweep, retaining the exact leaf maximum installed by `processnode`. -/
theorem otherNode_leaf_complete {ctx : Ctx} {nn inf tcLevel specFuel fuel
    level numcells : Nat} {cs bs : List Nat} {st : SearchSt}
    (hlevel : level = cs.length + 1) (hlevelN : level ≤ nn)
    (hbs : bs ≠ [])
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = ctx.n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level ctx.n = true)
    (hcinv : CodeCmpInv nn
      (cs ++ [(refine ctx level st.lab st.ptn st.active
        numcells).longcode]) bs
      (otherLeafSt ctx level numcells st).canoncode
      (otherLeafSt ctx level numcells st).canonlevel
      (otherLeafSt ctx level numcells st).eqlevCanon
      (otherLeafSt ctx level numcells st).compCanon)
    (hginv : CanongInv ctx (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hdone : ¬((processnode ctx level ctx.n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)) :
    NodeResult ctx tcLevel (specFuel + 1) (fuel + 1) level cs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells (some (incKey ctx bs st.canonlab))
      (some (keyMax (incKey ctx bs st.canonlab)
        (pathLeafKey ctx
          (cs ++ [(refine ctx level st.lab st.ptn st.active
            numcells).longcode])
          (refine ctx level st.lab st.ptn st.active numcells).lab)))
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  rw [otherNode_leaf_done_state ctx inf tcLevel fuel level numcells st
    hnum hdone]
  let code := (refine ctx level st.lab st.ptn st.active numcells).longcode
  let full := cs ++ [code]
  let pre : SearchSt :=
    { st with
      lab := (refine ctx level st.lab st.ptn st.active numcells).lab
      ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn
      active := (refine ctx level st.lab st.ptn st.active numcells).active
      numnodes := st.numnodes + 1 }
  let leaf := otherLeafSt ctx level numcells st
  have hfullLen : full.length = level := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hfullNe : full ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [full, List.length_append, List.length_singleton,
      List.length_nil] at hl
    omega
  have hleaf := processnode_leaf_read (ctx := ctx) (nn := nn)
    (cs := full) (bs := bs) (numcells := ctx.n) (st := leaf)
    (by simpa only [full, code, leaf] using hcinv) hginv
    (by rw [hfullLen]; exact hlevelN) hbs hfullNe
    (by simpa only [hfullLen, leaf] using hef) (by simp)
  obtain ⟨_, hread, _, _, _⟩ := hleaf
  have hframes := otherNodePrep_frames level code pre
  rcases hframes with
    ⟨hcanon, _, _, _, _, _, _, _, _, _, _, hlab, _⟩
  have hleafCanon : leaf.canonlab = st.canonlab := by
    change (otherNodePrep level code pre).canonlab = st.canonlab
    rw [hcanon]
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    change (otherNodePrep level code pre).lab = _
    rw [hlab]
  rw [hfullLen, hleafCanon, hleafLab] at hread
  have hfinish := (stInc_leafFinish ctx level
    (processnode ctx level ctx.n leaf).2).trans hread
  have hnode : nodeKey ctx tcLevel (specFuel + 1) level cs st numcells =
      pathLeafKey ctx full
        (refine ctx level st.lab st.ptn st.active numcells).lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey]
  apply NodeResult.complete
  · apply NodeSound.ofExact
    rw [incMax, hnode]
  · rfl
  · exact canonlevel_ne_zero_of_stInc hfinish
  · simpa only [leaf] using hfinish
  · rw [incMax, hnode]

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
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
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
  exact .complete rfl (.refl ctx bound best) hinstalled hread tcell cursor
    hcover fun o ho => no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

/-- With positive loop fuel, an absent next child completes the off-path
sweep rather than exhausting it. -/
theorem otherLoop_done (ctx : Ctx)
    (inf tcLevel specFuel runFuel loopFuel level numcells tc tv1 : Nat)
    (cs : List Nat) (rsLab rsPtn : Array Nat) (len tcell : Nat)
    (cursor : Option Nat) (bound : Key) (st : SearchSt)
    (best : Option Key)
    (hinstalled : st.canonlevel ≠ 0) (hread : stInc ctx st = best)
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
  exact .complete rfl (.refl ctx bound best) hinstalled hread tcell cursor
    hcover fun o ho => no_child_after hnext rsLab[tc + o]! ho.2.1 ho.2.2

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
