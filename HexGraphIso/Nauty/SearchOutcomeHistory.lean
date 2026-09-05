/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeLoop
public import HexGraphIso.Nauty.SearchOutcomeReturn

public section

/-!
Reference-leaf history along the active search trail.

The mutable controls `gcaFirst` and `gcaCanon` say how far a leaf
reference may be used during an unwind.  They do not by themselves record
that the referenced leaf descends from every intervening active frame.
`RefTrail` supplies exactly that missing path history.  It is deliberately
separate from `RunInv`: the first leaf seeds it only after the initial
descent has finished.
-/

namespace Hex.GraphIso.Nauty

/-- Every active frozen frame has the expected labelling size, and each
installed leaf reference reaches all active frames no deeper than its
current greatest-common-ancestor control. -/
structure RefTrail (ctx : Ctx n) (current : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop where
  frameSize : ∀ target entry, target < current →
    trail target = some entry → entry.frame.rsLab.size = n
  first : ∀ target entry, target < current →
    target ≤ st.gcaFirst → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.firstlab
  canon : ∀ target entry, target < current →
    target ≤ st.gcaCanon → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.canonlab

namespace RefTrail

/-- The off-path comparison step leaves the first GCA control unchanged. -/
theorem otherLeaf_gcaFirst (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).gcaFirst = st.gcaFirst := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  simpa only [otherLeafSt, rs, base] using
    (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.1

/-- The off-path comparison step leaves the canonical GCA control
unchanged. -/
theorem otherLeaf_gcaCanon (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).gcaCanon = st.gcaCanon := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  simpa only [otherLeafSt, rs, base] using
    (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.1

/-- The off-path comparison step leaves the cheap-automorphism boundary
unchanged. -/
theorem otherLeaf_noncheaplevel (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (otherLeafSt ctx level numcells st).noncheaplevel =
      st.noncheaplevel := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  simpa only [otherLeafSt, rs, base] using
    (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.1

/-- The empty trail has no reference-history obligations. -/
theorem empty (ctx : Ctx n) (current : Nat) (st : SearchSt n) :
    RefTrail ctx current st FrameTrail.empty := by
  constructor
  · intro target entry _ hentry
    simp [FrameTrail.empty] at hentry
  · intro target entry _ _ hentry
    simp [FrameTrail.empty] at hentry
  · intro target entry _ _ hentry
    simp [FrameTrail.empty] at hentry

/-- Installing the first leaf seeds both reference histories from the
current descent, while retaining the accumulated frozen-frame sizes. -/
theorem firstterminal {ctx : Ctx n} {level : Nat} {st : SearchSt n}
    {trail : FrameTrail} (htrail : TrailOk ctx level st trail)
    (hsize : ∀ target entry, target < level →
      trail target = some entry → entry.frame.rsLab.size = n) :
    RefTrail ctx level (Nauty.firstterminal level st) trail := by
  constructor
  · exact hsize
  · intro target entry hlt _ hentry
    rw [firstterminal_firstlab]
    exact htrail.reach target entry hlt hentry
  · intro target entry hlt _ hentry
    rw [firstterminal_canonlab]
    exact htrail.reach target entry hlt hentry

/-- When both installed references are the current labelling, the active
trail itself supplies their complete history. -/
theorem ofCurrent {ctx : Ctx n} {current : Nat} {st : SearchSt n}
    {trail : FrameTrail} (htrail : TrailOk ctx current st trail)
    (hsize : ∀ target entry, target < current →
      trail target = some entry → entry.frame.rsLab.size = n)
    (hfirst : st.firstlab = st.lab) (hcanon : st.canonlab = st.lab) :
    RefTrail ctx current st trail := by
  constructor
  · exact hsize
  · intro target entry hlt _ hentry
    rw [hfirst]
    exact htrail.reach target entry hlt hentry
  · intro target entry hlt _ hentry
    rw [hcanon]
    exact htrail.reach target entry hlt hentry

/-- Reference history depends only on the two references and their GCA
controls. -/
theorem stateEq {ctx : Ctx n} {current : Nat} {st st' : SearchSt n}
    {trail : FrameTrail} (h : RefTrail ctx current st trail)
    (hfirstGca : st'.gcaFirst = st.gcaFirst)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanonGca : st'.gcaCanon = st.gcaCanon)
    (hcanon : st'.canonlab = st.canonlab) :
    RefTrail ctx current st' trail := by
  constructor
  · exact h.frameSize
  · intro target entry hlt hle hentry
    rw [hfirstGca] at hle
    rw [hfirst]
    exact h.first target entry hlt hle hentry
  · intro target entry hlt hle hentry
    rw [hcanonGca] at hle
    rw [hcanon]
    exact h.canon target entry hlt hle hentry

/-- Refinement and the off-path comparison step retain both reference
histories. -/
theorem otherLeaf {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : RefTrail ctx level st trail) :
    RefTrail ctx level (otherLeafSt ctx level numcells st) trail := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  have hf := otherNodePrep_frames level rs.longcode base
  apply h.stateEq
  · simpa only [otherLeafSt, rs, base] using hf.2.2.2.2.2.2.1
  · simpa only [otherLeafSt, rs, base] using hf.2.2.2.2.1
  · simpa only [otherLeafSt, rs, base] using hf.2.2.2.2.2.2.2.1
  · simpa only [otherLeafSt, rs, base] using hf.1

/-- The off-path comparison step preserves the ordering of the two GCA
controls while search remains active. -/
theorem otherLeaf_order {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (h : st.gcaFirst ≤ st.gcaCanon) :
    (otherLeafSt ctx level numcells st).gcaFirst ≤
      (otherLeafSt ctx level numcells st).gcaCanon := by
  rw [otherLeaf_gcaFirst, otherLeaf_gcaCanon]
  exact h

/-- Recovering an ancestor preserves both reference histories.  The
canonical control may be clamped to the recovered level, which only
weakens its reach obligation. -/
theorem recover {ctx : Ctx n} {current level inf : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : RefTrail ctx current st trail)
    (hle : level ≤ current) :
    RefTrail ctx level (Nauty.recover n inf level st) trail := by
  obtain ⟨hcanon, -, -, -, hfirst, -, hgcaFirst, -, -, -⟩ :=
    recover_frames n inf level st
  constructor
  · intro target entry hlt hentry
    exact h.frameSize target entry (Nat.lt_of_lt_of_le hlt hle) hentry
  · intro target entry hlt hbound hentry
    rw [hgcaFirst] at hbound
    rw [hfirst]
    exact h.first target entry (Nat.lt_of_lt_of_le hlt hle) hbound hentry
  · intro target entry hlt hbound hentry
    rw [recover_gcaCanon] at hbound
    rw [hcanon]
    apply h.canon target entry (Nat.lt_of_lt_of_le hlt hle) _ hentry
    split at hbound
    · omega
    · exact hbound

/-- A leaf event retains the first history.  It either retains the
canonical history as well or installs the current reached labelling as
the new canonical reference. -/
theorem processnode {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : RefTrail ctx level st trail)
    (htrail : TrailOk ctx level st trail) :
    RefTrail ctx level (Nauty.processnode ctx level numcells st).2
      trail := by
  obtain ⟨-, -, -, -, hfirst, -, hgcaFirst, -, -⟩ :=
    processnode_frames ctx level numcells st
  constructor
  · exact h.frameSize
  · intro target entry hlt hbound hentry
    rw [hgcaFirst] at hbound
    rw [hfirst]
    exact h.first target entry hlt hbound hentry
  · intro target entry hlt hbound hentry
    rcases processnode_canonGuide ctx level numcells st with hold | hnew
    · rw [hold.1] at hbound
      rw [hold.2]
      exact h.canon target entry hlt hbound hentry
    · rw [hnew.2]
      exact htrail.reach target entry hlt hentry

/-- `processnode` preserves the ordering of the first and canonical GCA
controls.  Installing a new canonical leaf parks its control at the
current level, above the bounded first control. -/
theorem processnode_order {ctx : Ctx n} {level numcells : Nat}
    {st : SearchSt n} (horder : st.gcaFirst ≤ st.gcaCanon)
    (hfirstBound : st.gcaFirst ≤ level) :
    (Nauty.processnode ctx level numcells st).2.gcaFirst ≤
      (Nauty.processnode ctx level numcells st).2.gcaCanon := by
  have hfirst := (processnode_frames ctx level numcells st).2.2.2.2.2.2.1
  rw [hfirst]
  rcases processnode_canonGuide ctx level numcells st with hold | hnew
  · rw [hold.1]
    exact horder
  · rw [hnew.1]
    exact hfirstBound

/-- Leaf cleanup changes neither installed reference nor its GCA
control. -/
theorem leafFinish {ctx : Ctx n} {level current : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : RefTrail ctx current st trail) :
    RefTrail ctx current (Nauty.leafFinish ctx level st) trail := by
  unfold Nauty.leafFinish
  split
  · simp only
    split <;> exact h.stateEq rfl rfl rfl rfl
  · simp only
    split <;> exact h.stateEq rfl rfl rfl rfl

/-- Recovery preserves GCA ordering provided the first control is no
deeper than the receiving frame. -/
theorem recover_order {ctx : Ctx n} {level inf : Nat} {st : SearchSt n}
    (horder : st.gcaFirst ≤ st.gcaCanon)
    (hfirstBound : st.gcaFirst ≤ level) :
    (Nauty.recover n inf level st).gcaFirst ≤
      (Nauty.recover n inf level st).gcaCanon := by
  have hfirst := (recover_frames n inf level st).2.2.2.2.2.2.1
  rw [hfirst, recover_gcaCanon]
  split
  · exact hfirstBound
  · exact horder

/-- Pushing a child frame extends reference history.  At the new frame,
the loop's two reference receipts discharge the cases whose GCA control
is exactly the parent level. -/
theorem push {ctx : Ctx n} {level : Nat} {st : SearchSt n}
    {trail : FrameTrail} {entry : TrailEntry}
    (h : RefTrail ctx level st trail)
    (hfirstBound : st.gcaFirst ≤ level)
    (hcanonBound : st.gcaCanon ≤ level)
    (hsize : entry.frame.rsLab.size = n)
    (hfirst : st.gcaFirst = level →
      cellsPerm entry.frame.rsPtn level entry.frame.rsLab st.firstlab)
    (hcanon : st.gcaCanon = level →
      cellsPerm entry.frame.rsPtn level entry.frame.rsLab st.canonlab) :
    RefTrail ctx (level + 1) st (trail.push level entry) := by
  constructor
  · intro target found hlt hfound
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | rfl
    · rw [FrameTrail.push_of_ne _ entry (Nat.ne_of_lt hold)] at hfound
      exact h.frameSize target found hold hfound
    · rw [FrameTrail.push_self] at hfound
      have : found = entry := Option.some.inj hfound.symm
      subst found
      exact hsize
  · intro target found hlt hbound hfound
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | rfl
    · rw [FrameTrail.push_of_ne _ entry (Nat.ne_of_lt hold)] at hfound
      exact h.first target found hold hbound hfound
    · rw [FrameTrail.push_self] at hfound
      have : found = entry := Option.some.inj hfound.symm
      subst found
      apply hfirst
      omega
  · intro target found hlt hbound hfound
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hold | rfl
    · rw [FrameTrail.push_of_ne _ entry (Nat.ne_of_lt hold)] at hfound
      exact h.canon target found hold hbound hfound
    · rw [FrameTrail.push_self] at hfound
      have : found = entry := Option.some.inj hfound.symm
      subst found
      apply hcanon
      omega

/-- The concrete child state created by a verified sweep inherits both
reference histories.  `FrameRefs` supplies the new parent-frame case;
all older frames come directly from the incoming history. -/
theorem LoopInv.childHistory {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (h : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hhist : RefTrail ctx level st trail)
    (offset currentOffset : Nat) :
    RefTrail ctx (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]!
        cosetindex := coset }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  have hpushed := hhist.push h.run.firstBound h.run.canonBound
    h.frozenLabSize
    (fun heq => (h.refs.first heq).choose_spec.2.2.2)
    (fun heq => (h.refs.canon heq).choose_spec.2.2.2)
    (entry := ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
  apply hpushed.stateEq <;> rfl

/-- A scatter from the first reference onto the current labelling
stabilizes every active frame to which `gcaFirst` permits a return. -/
theorem firstStab {ctx : Ctx n} {current : Nat} {st : SearchSt n}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hfirstSize : st.firstlab.size = n)
    (hbelow : st.gcaFirst < current)
    (hmap : ∀ i, i < n →
      gamma[st.firstlab[i]!]! = st.lab[i]!) :
    ∀ target entry, Int.ofNat target ≤ Int.ofNat st.gcaFirst →
      trail target = some entry →
      CellStab entry.frame.rsPtn target entry.frame.rsLab gamma := by
  intro target entry hbound hentry
  have hnat : target ≤ st.gcaFirst := Int.ofNat_le.mp hbound
  have hlt : target < current := Nat.lt_of_le_of_lt hnat hbelow
  exact cellStab_of_scatter
    (htrail.ptnSize target entry hlt hentry)
    (h.frameSize target entry hlt hentry) hfirstSize
    (htrail.endClosed target entry hlt hentry)
    (h.first target entry hlt hnat hentry)
    (htrail.reach target entry hlt hentry) hmap

/-- Appending a first-reference scatter preserves the complete
return-stabilization obligation at `gcaFirst`. -/
theorem firstPushStab {ctx : Ctx n} {current : Nat} {st out : SearchSt n}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hfirstSize : st.firstlab.size = n)
    (hbelow : st.gcaFirst < current)
    (hprev : ReturnStab trail (Int.ofNat st.gcaFirst) st)
    (hpush : out.genTrace = st.genTrace.push gamma)
    (hmap : ∀ i, i < n →
      gamma[st.firstlab[i]!]! = st.lab[i]!) :
    ReturnStab trail (Int.ofNat st.gcaFirst) out := by
  exact hprev.pushGen hpush
    (h.firstStab htrail hfirstSize hbelow hmap)

/-- A scatter from the canonical reference onto the current labelling
stabilizes every active frame through any bound no deeper than
`gcaCanon`.  The smaller bound is needed by code two's orbit return to
`gcaFirst`. -/
theorem canonStabTo {ctx : Ctx n} {current limit : Nat} {st : SearchSt n}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hcanonSize : st.canonlab.size = n)
    (hle : limit ≤ st.gcaCanon) (hbelow : limit < current)
    (hmap : ∀ i, i < n →
      gamma[st.canonlab[i]!]! = st.lab[i]!) :
    ∀ target entry, Int.ofNat target ≤ Int.ofNat limit →
      trail target = some entry →
      CellStab entry.frame.rsPtn target entry.frame.rsLab gamma := by
  intro target entry hbound hentry
  have hlimit : target ≤ limit := Int.ofNat_le.mp hbound
  have hnat : target ≤ st.gcaCanon := Nat.le_trans hlimit hle
  have hlt : target < current := Nat.lt_of_le_of_lt hlimit hbelow
  exact cellStab_of_scatter
    (htrail.ptnSize target entry hlt hentry)
    (h.frameSize target entry hlt hentry) hcanonSize
    (htrail.endClosed target entry hlt hentry)
    (h.canon target entry hlt hnat hentry)
    (htrail.reach target entry hlt hentry) hmap

/-- Appending a canonical-reference scatter preserves the complete
return-stabilization obligation through any resumable bound below its
GCA. -/
theorem canonPushStabTo {ctx : Ctx n} {current limit : Nat}
    {st out : SearchSt n} {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hcanonSize : st.canonlab.size = n)
    (hle : limit ≤ st.gcaCanon) (hbelow : limit < current)
    (hprev : ReturnStab trail (Int.ofNat limit) st)
    (hpush : out.genTrace = st.genTrace.push gamma)
    (hmap : ∀ i, i < n →
      gamma[st.canonlab[i]!]! = st.lab[i]!) :
    ReturnStab trail (Int.ofNat limit) out := by
  exact hprev.pushGen hpush
    (h.canonStabTo htrail hcanonSize hle hbelow hmap)

/-- The exact canonical-GCA instance of `canonStabTo`. -/
theorem canonStab {ctx : Ctx n} {current : Nat} {st : SearchSt n}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hcanonSize : st.canonlab.size = n)
    (hbelow : st.gcaCanon < current)
    (hmap : ∀ i, i < n →
      gamma[st.canonlab[i]!]! = st.lab[i]!) :
    ∀ target entry, Int.ofNat target ≤ Int.ofNat st.gcaCanon →
      trail target = some entry →
      CellStab entry.frame.rsPtn target entry.frame.rsLab gamma := by
  exact h.canonStabTo htrail hcanonSize (Nat.le_refl _) hbelow hmap

/-! # Concrete leaf admissions -/

/-- A successful code-one admission extends the inherited ancestor
stabilization and returns exactly to the first-reference GCA. -/
theorem processnodeFirstStab {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n)
    (h : RefTrail ctx level st trail)
    (htrail : TrailOk ctx level st trail) (hrefs : LeafRefsOk G st)
    (hprev : ReturnStab trail (Int.ofNat st.gcaFirst) st)
    (hbelow : st.gcaFirst < level)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx
      (firstScatter n st.firstlab st.lab) = true) :
    ReturnStab trail (Nauty.processnode ctx level numcells st).1
      (Nauty.processnode ctx level numcells st).2 := by
  have hreturn :=
    (processnode_auto (st := st) heq hsent hnc hpass).1
  rw [hreturn]
  let gamma := (List.range n).foldl
    (fun w i => w.set! st.firstlab[i]! st.lab[i]!)
    (Array.replicate n 0)
  have hfirstOk := labOk_of_reach hrefs.firstSize hrefs.firstReach
  have hinj := labInj_of_reach hrefs.firstSize hn0 hrefs.firstReach
  have hmap : ∀ i, i < n →
      gamma[st.firstlab[i]!]! = st.lab[i]! := by
    intro i hi
    apply foldl_scatter_getElem
      (fun a b ha hb hab => hinj.eq_of_getElem! ha hb hab)
      (fun j hj => by
        rw [Array.size_replicate]
        exact hfirstOk j (by rw [hrefs.firstSize]; omega))
      (Nat.le_refl _) hi
  have hpush : (Nauty.processnode ctx level numcells st).2.genTrace =
      st.genTrace.push gamma := by
    exact processnode_genTrace_first heq hsent hnc
      (by simpa only [firstScatter] using hpass)
  apply h.firstPushStab htrail hrefs.firstSize hbelow
    hprev hpush hmap

/-- A code-two admission stabilizes either advertised return: the direct
canonical return uses the full canonical history, while the special orbit
return uses `gcaFirst ≤ gcaCanon`. -/
theorem processnodeTiedStab {G : Colored n k} {ctx : Ctx n}
    {level numcells : Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n)
    (h : RefTrail ctx level st trail)
    (htrail : TrailOk ctx level st trail) (hrefs : LeafRefsOk G st)
    (horder : st.gcaFirst ≤ st.gcaCanon)
    (hprev : ReturnStab trail (Int.ofNat st.gcaFirst) st)
    (hcanonBelow : st.gcaCanon < level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    ReturnStab trail (Int.ofNat st.gcaFirst)
      (Nauty.processnode ctx level numcells st).2 := by
  let gamma := (List.range n).foldl
    (fun w i => w.set! st.canonlab[i]! st.lab[i]!)
    (Array.replicate n 0)
  have hcanonOk := labOk_of_reach hrefs.canonSize hrefs.canonReach
  have hinj := labInj_of_reach hrefs.canonSize hn0 hrefs.canonReach
  have hmap : ∀ i, i < n →
      gamma[st.canonlab[i]!]! = st.lab[i]! := by
    intro i hi
    apply foldl_scatter_getElem
      (fun a b ha hb hab => hinj.eq_of_getElem! ha hb hab)
      (fun j hj => by
        rw [Array.size_replicate]
        exact hcanonOk j (by rw [hrefs.canonSize]; omega))
      (Nat.le_refl _) hi
  have hpush : (Nauty.processnode ctx level numcells st).2.genTrace =
      st.genTrace.push gamma := by
    exact processnode_genTrace_canon hef hnc hcc hge htie
  apply h.canonPushStabTo htrail hrefs.canonSize horder
    (Nat.lt_of_le_of_lt horder hcanonBelow) hprev hpush hmap

end RefTrail

namespace ReturnStab

/-- Refinement and the off-path comparison step leave the generator
store unchanged. -/
theorem otherLeaf {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {trail : FrameTrail} {r : Int} (h : ReturnStab trail r st) :
    ReturnStab trail r (otherLeafSt ctx level numcells st) := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let base : SearchSt n :=
    { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      numnodes := st.numnodes + 1 }
  apply h.ofGenTraceEq
  simpa only [otherLeafSt, rs, base] using
    (otherNodePrep_store level rs.longcode base).1

end ReturnStab

end Hex.GraphIso.Nauty
