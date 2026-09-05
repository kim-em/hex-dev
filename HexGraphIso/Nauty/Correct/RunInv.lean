/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Frames
public import HexGraphIso.Nauty.Correct.Unwind
import all HexGraphIso.Nauty.Search

public section

/-!
The live hypotheses shared by the corrected mutual search induction.

`RefTrail` supplies the reference-leaf path history along the active
trail, `EventOut` records the result-side state a recursive node returns,
and the closing `cosetindex` equations say when orbit-return coverage may
read that cursor.
-/

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
    RefTrail ctx current (Nauty.leafFinish level st) trail := by
  unfold Nauty.leafFinish
  split
  · simp only
    split <;> exact h.stateEq rfl rfl rfl rfl
  · simp only
    split <;> exact h.stateEq rfl rfl rfl rfl

/-- Recovery preserves GCA ordering provided the first control is no
deeper than the receiving frame. -/
theorem recover_order {level inf : Nat} {st : SearchSt n}
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

/-!
The result-side state shared by recursive node outcomes.

The executable can return a state whose comparison path is deeper than
the caller receiving it.  `EventOut` existentially records that full path,
its incumbent code list, and the event depth, while exposing only the
entry prefix needed by the caller.  Return-indexed stabilization travels
with the same concrete result state.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A recursive result state with a faithful comparison path and every
ancestor stabilization obligation enabled by its returned level. -/
inductive EventOut (G : Colored n k) (ctx : Ctx n) (tcLevel : Nat)
    (stem fs : List Nat) (out : SearchSt n) (best : Option (Key n))
    (trail : FrameTrail) (r : Int) : Prop where
  | intro (current : Nat) (codes bestCodes : List Nat)
      (event : RunEvent G ctx tcLevel current codes bestCodes fs out best
        trail)
      (depth : current = codes.length)
      (stemEq : codes.take stem.length = stem)
      (past : stem.length < current)
      (returned : r ≤ Int.ofNat current)
      (stable : ReturnStab trail (min r (Int.ofNat out.gcaFirst)) out)
      (history : RefTrail ctx current out trail)

namespace RunEvent

/-- Every event state reads back the semantic incumbent recorded by its
comparison machine.  The row-rejection arm uses its deliberately reset
zero-sign machine. -/
theorem read {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    stInc ctx st = best := by
  have hread : stInc ctx st = ghostInc ctx bs st.canonlab := by
    rcases h.machines with hplain | hreset
    · apply stInc_eq_ghost hplain.2
      omega
    · exact stInc_eq_ghost hreset.2 (by decide)
  rw [hread, ghostInc]
  simp only [h.bestCodes, ↓reduceIte, h.incumbent]

/-- Fixed-point bookkeeping changes none of an event state's logical
fields. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (fixedpts : VSet n) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with fixedpts := fixedpts } best trail := by
  let st' : SearchSt n := { st with fixedpts := fixedpts }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Clearing the one-shot short-prune flag changes none of an event
state's logical fields. -/
theorem clearShort {G : Colored n k} {ctx : Ctx n}
    {tcLevel current : Nat} {cs bs fs : List Nat} {st : SearchSt n}
    {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with needshortprune := false } best trail := by
  let st' : SearchSt n := { st with needshortprune := false }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive,
    h.canonPositive, h.firstBound, h.canonBound, h.bestCodes,
    h.incumbent⟩

/-- Updating the first-path agreement counter changes none of an event
state's logical fields. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx n}
    {tcLevel current allsamelevel : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with allsamelevel := allsamelevel } best trail := by
  let st' : SearchSt n := { st with allsamelevel := allsamelevel }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- Installing the first-path return controls preserves an event state
once the caller supplies the new guide and numeric bounds. -/
theorem setFirst {G : Colored n k} {ctx : Ctx n}
    {tcLevel current gcaFirst stabvertex : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hguides : GuideStore ctx tcLevel current
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail)
    (hpositive : 0 < gcaFirst) (hbound : gcaFirst ≤ current) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
      best trail := by
  let st' : SearchSt n :=
    { st with gcaFirst := gcaFirst, stabvertex := stabvertex }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.ofFrames rfl rfl rfl,
    hrefs, hguides,
    h.trailOk.stateEq rfl rfl, hpositive,
    h.canonPositive, hbound, h.canonBound, h.bestCodes, h.incumbent⟩

/-- Parking the cheap-automorphism boundary above the current event level
preserves the event invariant. -/
theorem park {G : Colored n k} {ctx : Ctx n}
    {tcLevel current boundary : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel current cs bs fs st best trail)
    (hpos : 0 < boundary) (hcurrent : current ≤ boundary) :
    RunEvent G ctx tcLevel current cs bs fs
      { st with noncheaplevel := boundary } best trail := by
  let st' : SearchSt n := { st with noncheaplevel := boundary }
  have hrefs : LeafRefsOk G st' :=
    ⟨h.leafRefs.firstSize, h.leafRefs.firstReach,
      h.leafRefs.canonSize, h.leafRefs.canonReach⟩
  exact ⟨h.machines, h.firstInv, h.canongInv,
    genTraceOk_of_eq (st := st) (st' := st') rfl h.genTraceOk,
    autosOk_of_eq (st := st) (st' := st') rfl h.autosOk,
    h.workspace.ofFields rfl rfl, h.cheap.park hpos hcurrent, hrefs,
    h.guides.stateEq rfl rfl rfl rfl, h.trailOk.stateEq rfl rfl,
    h.firstPositive, h.canonPositive, h.firstBound, h.canonBound,
    h.bestCodes, h.incumbent⟩

/-- The comparison-blind cleanup after an empty leaf sweep preserves an
event state. -/
theorem leafFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel level : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunEvent G ctx tcLevel level cs bs fs st best trail) :
    RunEvent G ctx tcLevel level cs bs fs
      (Nauty.leafFinish level st) best trail := by
  unfold Nauty.leafFinish
  split
  · simp only
    split
    · exact h.clearShort.park (by omega) (by omega)
    · exact h.clearShort
  · simp only
    split
    · exact h.park (by omega) (by omega)
    · exact h

end RunEvent

namespace ReturnStab

/-- Leaf cleanup leaves the recorded-generator store unchanged. -/
theorem leafFinish {level : Nat} {st : SearchSt n}
    {trail : FrameTrail} {r : Int} (h : ReturnStab trail r st) :
    ReturnStab trail r (Nauty.leafFinish level st) := by
  apply h.ofGenTraceEq
  unfold Nauty.leafFinish
  split
  · simp only
    split <;> rfl
  · simp only
    split <;> rfl

end ReturnStab

namespace EventOut

/-- A packaged event reads back its semantic incumbent. -/
theorem read {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    stInc ctx out = best := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.read

/-- Every event output retains a full-size canonical reference. -/
theorem canonSize {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    out.canonlab.size = n := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.leafRefs.canonSize

/-- Every pair in a result workspace remains valid at the initial coloured
partition. -/
theorem autosOk {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    AutosOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 out.autos := by
  cases h with
  | intro _ _ _ event _ _ _ _ _ _ => exact event.autosOk

/-- Every event output exposes stabilization through the smaller of its
return target and live first-reference GCA.  Direct carrier returns need
no stronger statement, while the orbit-return arm targets this GCA. -/
theorem returnStab {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    ReturnStab trail (min r (Int.ofNat out.gcaFirst)) out := by
  cases h with
  | intro _ _ _ _ _ _ _ _ stable _ => exact stable

/-- Recovering an event that returned exactly to `level` produces the
stable parent-loop state and retains its generator stabilization. -/
theorem recoverRun {G : Colored n k} {ctx : Ctx n} {tcLevel level inf numcells : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hreturn : r = Int.ofNat level) (hstem : stem.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hfirst : out.gcaFirst ≤ level)
    (hok : SearchOk G level numcells
      (Nauty.recover n inf level out)) :
    ∃ bs,
      RunInv G ctx tcLevel level stem bs fs numcells
          (Nauty.recover n inf level out) best trail ∧
        ReturnStab trail
          (Int.ofNat (Nauty.recover n inf level out).gcaFirst)
          (Nauty.recover n inf level out) ∧
        RefTrail ctx level (Nauty.recover n inf level out) trail := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      rw [hreturn] at returned stable
      have hle : level ≤ current := Int.ofNat_le.mp returned
      have hpath : level ≤ codes.length := by omega
      have hrun := event.recover hle hlevel hinf hpath hfirst hok
      have htake : codes.take level = stem := by
        rw [← hstem]
        exact stemEq
      rw [htake] at hrun
      have hfirstEq : (Nauty.recover n inf level out).gcaFirst =
          out.gcaFirst :=
        (recover_frames n inf level out).2.2.2.2.2.2.1
      have hfirst' : Int.ofNat out.gcaFirst ≤ Int.ofNat level :=
        Int.ofNat_le.mpr hfirst
      have hmin : min (Int.ofNat level) (Int.ofNat out.gcaFirst) =
          Int.ofNat out.gcaFirst := by omega
      rw [hmin] at stable
      rw [hfirstEq]
      exact ⟨bestCodes, hrun, stable.recover inf level,
        history.recover hle⟩

/-- A stable state with a nonpositive comparison sign is an event output
at its own code depth. -/
theorem ofRun {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail} {r : Int}
    (h : RunInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hdepth : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hreturn : r ≤ Int.ofNat level) (hnonpositive : st.compCanon ≤ 0)
    (hstable : ReturnStab trail (min r (Int.ofNat st.gcaFirst)) st)
    (hhistory : RefTrail ctx level st trail) :
    EventOut G ctx tcLevel stem fs st best trail r :=
  .intro level codes bs (h.event hnonpositive) hdepth hstem hpast hreturn
    hstable hhistory

/-- Weakening the returned level preserves an event output. -/
theorem lower {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r r' : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (hle : r' ≤ r) :
    EventOut G ctx tcLevel stem fs out best trail r' := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      have hmin : min r' (Int.ofNat out.gcaFirst) ≤
          min r (Int.ofNat out.gcaFirst) := by omega
      exact .intro current codes bestCodes event depth stemEq past
        (Int.le_trans hle returned) (stable.lower hmin) history

/-- Fixed-point cleanup preserves the full result-side package. -/
theorem setFixed {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r)
    (fixedpts : VSet n) :
    EventOut G ctx tcLevel stem fs { out with fixedpts := fixedpts }
      best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes (event.setFixed fixedpts)
        depth stemEq past returned (stable.setFixed fixedpts)
        (history.stateEq rfl rfl rfl rfl)

/-- Clearing the short-prune request preserves the full result package. -/
theorem clearShort {G : Colored n k} {ctx : Ctx n} {tcLevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with needshortprune := false } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes event.clearShort depth stemEq past
        returned stable.clearShort (history.stateEq rfl rfl rfl rfl)

/-- Updating the first-path agreement counter preserves the full result
package. -/
theorem setAllsame {G : Colored n k} {ctx : Ctx n} {tcLevel allsamelevel : Nat}
    {stem fs : List Nat} {out : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail} {r : Int}
    (h : EventOut G ctx tcLevel stem fs out best trail r) :
    EventOut G ctx tcLevel stem fs
      { out with allsamelevel := allsamelevel } best trail r := by
  cases h with
  | intro current codes bestCodes event depth stemEq past returned stable
      history =>
      exact .intro current codes bestCodes event.setAllsame depth stemEq past
        returned (stable.setAllsame allsamelevel)
        (history.stateEq rfl rfl rfl rfl)

end EventOut

end Hex.GraphIso.Nauty

/-!
Corrected node outcomes coupled to their result-side invariants.
-/

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- An output trail retains every frame that was active on entry.  A
node may additionally replace deeper scratch entries used by its own
recursive sweep. -/
@[expose] def TrailExt (level : Nat) (before after : FrameTrail) : Prop :=
  ∀ target, target < level → after target = before target

theorem TrailExt.refl (level : Nat) (trail : FrameTrail) :
    TrailExt level trail trail := fun _ _ => rfl

theorem TrailExt.trans {level : Nat} {a b c : FrameTrail}
    (hab : TrailExt level a b) (hbc : TrailExt level b c) :
    TrailExt level a c := fun target htarget =>
  (hbc target htarget).trans (hab target htarget)

/-- Retaining a pushed child trail retains every older parent frame. -/
theorem TrailExt.ofPush {level : Nat} {trail out : FrameTrail}
    {entry : TrailEntry}
    (h : TrailExt (level + 1) (trail.push level entry) out) :
    TrailExt level trail out := by
  intro target htarget
  rw [h target (by omega), FrameTrail.push_of_ne]
  omega

/-- Retaining a pushed child trail keeps the newly active parent frame
at its exact level. -/
theorem TrailExt.pushAt {level : Nat} {trail out : FrameTrail}
    {entry : TrailEntry}
    (h : TrailExt (level + 1) (trail.push level entry) out) :
    out level = some entry := by
  rw [h level (by omega), FrameTrail.push_self]

/-- Location evidence can be moved between trails that agree at the
unwind target. -/
theorem Unwind.Located.retrail {ctx : Ctx n} {tcLevel target : Nat}
    {out : SearchSt n} {best : Option (Key n)} {source dest : FrameTrail}
    {payload : Unwind ctx tcLevel target out best}
    (h : payload.Located source) (heq : source target = dest target) :
    payload.Located dest := by
  cases h with
  | first anchor carrier located =>
      apply Unwind.Located.first anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← heq]
      exact located
  | canon anchor carrier located =>
      apply Unwind.Located.canon anchor carrier
      unfold Anchor.Located at located ⊢
      rw [← heq]
      exact located
  | orbit payload => exact .orbit payload

/-- A loop receipt depends on its trail only below the loop level. -/
theorem LoopReceipt.retrail {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat} {cs : List Nat}
    {rsLab rsPtn : Array Nat} {tc len numcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {st out : SearchSt n}
    {best outBest : Option (Key n)} {source dest : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopReceipt source ctx tcLevel specFuel runFuel loopFuel level cs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest r) :
    LoopReceipt dest ctx tcLevel specFuel runFuel loopFuel level cs rsLab
      rsPtn tc len numcells tcell cursor bound st out best outBest r := by
  cases h with
  | complete returned sound installed read finalSet finalCursor cover empty =>
      exact .complete returned sound installed read finalSet finalCursor
        cover empty
  | unwind sound target returned below payload located =>
      exact .unwind sound target returned below payload
        (located.retrail (htrail target below))
  | pruned target returned below sound installed read full =>
      exact .pruned target returned below sound installed read full
  | exhausted returned sound finalSet finalCursor cover progress bounded =>
      exact .exhausted returned sound finalSet finalCursor cover progress
        bounded

/-- The semantic node receipt and the concrete result state produced by
one recursive node call. -/
structure NodeOutcome (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  receipt : NodeReceipt receiptTrail ctx tcLevel specFuel runFuel level cs st out
    numcells best outBest r
  event : EventOut G ctx tcLevel cs fs out outBest eventTrail r
  preserved : TrailExt level receiptTrail eventTrail

/-- Forgetting the concrete result invariant recovers the corrected
semantic node result consumed by the root reduction. -/
theorem NodeOutcome.toResult {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeResult ctx tcLevel specFuel runFuel level cs st out numcells best
      outBest r :=
  h.receipt.toResult

/-- At a parent boundary, a child outcome either supplies its exact
subtree maximum or a located unwind whose generator store stabilizes the
receiving frozen frame. -/
theorem NodeOutcome.parentReturn {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    {trail eventTrail : FrameTrail} {entry : TrailEntry}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel (level + 1) cs fs st
      out numcells best outBest (trail.push level entry) eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level)) :
    outBest = some (incMax best
        (nodeKey ctx tcLevel specFuel (level + 1) cs st numcells)) ∨
      ∃ payload : Unwind ctx tcLevel level out outBest,
        payload.Located (trail.push level entry) ∧
          payload.FrameStable entry.frame.rsPtn level entry.frame.rsLab := by
  cases h.receipt with
  | complete sound returned installed read full => exact Or.inl full
  | unwind sound target returned below payload located =>
      have hle : level ≤ target := by
        apply Int.ofNat_le.mp
        rw [returned] at hstay
        exact Int.not_lt.mp hstay
      have htarget : target = level := by omega
      subst target
      right
      refine ⟨payload, located, ?_⟩
      rw [returned] at h
      apply h.event.returnStab.frameStable
      exact h.preserved.pushAt
  | pruned sound target returned below installed read full =>
      exact Or.inl full
  | exhausted empty => exact (hfuel empty).elim

/-- A positive-fuel child that does not unwind past its parent returns
exactly to that parent level. -/
theorem NodeOutcome.parentEq {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells : Nat} {cs fs : List Nat}
    {st out : SearchSt n} {best outBest : Option (Key n)} {r : Int}
    {receiptTrail eventTrail : FrameTrail}
    (h : NodeOutcome G ctx tcLevel specFuel runFuel (level + 1) cs fs st
      out numcells best outBest receiptTrail eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level)) :
    r = Int.ofNat level := by
  cases h.receipt with
  | complete sound returned installed read full =>
      calc
        r = Int.ofNat (level + 1) - 1 := returned
        _ = Int.ofNat level := by simp
  | unwind sound target returned below payload located =>
      have hnot : ¬(Int.ofNat target < Int.ofNat level) := by
        rwa [returned] at hstay
      have hle : level ≤ target := Int.ofNat_le.mp (Int.not_lt.mp hnot)
      have heq : target = level := by omega
      exact returned.trans (congrArg Int.ofNat heq)
  | pruned sound target returned below installed read full =>
      have hnot : ¬(target < Int.ofNat level) := by
        rwa [returned] at hstay
      have heq : target = Int.ofNat level := by
        rw [show Int.ofNat (level + 1) = Int.ofNat level + 1 by simp]
          at below
        omega
      exact returned.trans heq
  | exhausted empty => exact (hfuel empty).elim

/-- An off-path node additionally leaves the first-path guide unchanged.
It also preserves live guide ordering; unlike a first-path node, it never
raises `gcaFirst` while returning through its child loop.  These are the
facts its parent needs before recovering a completed child. -/
structure OtherOutcome (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel level : Nat) (cs fs : List Nat)
    (st out : SearchSt n) (numcells : Nat) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail) (r : Int) : Prop where
  node : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
    numcells best outBest receiptTrail eventTrail r
  firstGuide : out.gcaFirst = st.gcaFirst
  order : out.gcaFirst ≤ out.gcaCanon
  canonGuide :
    (out.gcaCanon = st.gcaCanon ∧ out.canonlab = st.canonlab) ∨
      (level ≤ out.gcaCanon ∧
        cellsPerm st.ptn level st.lab out.canonlab)

/-- The integer return represented by a loop result.  Exhausting the
sweep completes its parent node one level up. -/
@[expose] def loopReturn (level : Nat) : Option Int → Int
  | some r => r
  | none => Int.ofNat level - 1

/-- A loop receipt coupled to the concrete result invariant ultimately
returned by its parent node.  `stem` is the parent node's entry prefix;
the loop's own `codes` include that node's refinement code. -/
structure LoopOutcome (G : Colored n k) (ctx : Ctx n)
    (tcLevel specFuel runFuel loopFuel level : Nat)
    (stem codes fs : List Nat) (rsLab rsPtn : Array Nat)
    (tc len numcells : Nat) (tcell : VSet n) (cursor : Option Nat) (bound : Key n)
    (st out : SearchSt n) (best outBest : Option (Key n))
    (receiptTrail eventTrail : FrameTrail)
    (r : Option Int) : Prop where
  receipt : LoopReceipt receiptTrail ctx tcLevel specFuel runFuel loopFuel level
    codes rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest r
  event : EventOut G ctx tcLevel stem fs out outBest eventTrail
    (loopReturn level r)
  preserved : TrailExt level receiptTrail eventTrail

/-- A loop that returns an integer supplies its parent node outcome. -/
theorem LoopOutcome.toNodeSome {G : Colored n k} {ctx : Ctx n}
    {tcLevel nodeSpecFuel loopSpecFuel nodeRunFuel runFuel loopFuel level : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (hbound : bound = nodeKey ctx tcLevel nodeSpecFuel level nodeCs nodeSt
      nodeNumcells)
    (h : LoopOutcome G ctx tcLevel loopSpecFuel runFuel loopFuel level nodeCs
      loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      out best outBest receiptTrail eventTrail (some r)) :
    NodeOutcome G ctx tcLevel nodeSpecFuel nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells best outBest receiptTrail eventTrail r := by
  exact ⟨NodeReceipt.ofLoopSome hbound h.receipt, h.event, h.preserved⟩

/-- A completed loop with sufficient cursor fuel supplies its parent
node's completed outcome. -/
theorem LoopOutcome.toNodeNone {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel nodeRunFuel runFuel loopFuel level tail : Nat}
    {nodeCs loopCs fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len nodeNumcells loopNumcells : Nat} {tcell : VSet n}
    {cursor : Option Nat} {bound : Key n} {nodeSt loopSt out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    (hbound : bound = nodeKey ctx tcLevel (specFuel + 1) level nodeCs
      nodeSt nodeNumcells)
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hfuel : n < cursorRank cursor + loopFuel)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level nodeCs
      loopCs fs rsLab rsPtn tc len loopNumcells tcell cursor bound loopSt
      out best outBest receiptTrail eventTrail none) :
    NodeOutcome G ctx tcLevel (specFuel + 1) nodeRunFuel level nodeCs fs
      nodeSt out nodeNumcells best outBest receiptTrail eventTrail
      (Int.ofNat level - 1) := by
  exact ⟨NodeReceipt.ofLoopNone hbound hchildren hlen hfuel h.receipt,
    h.event, h.preserved⟩

/-- Prepending a semantic loop fragment leaves the concrete result
package unchanged. -/
theorem LoopOutcome.prefix {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st recSt out : SearchSt n} {best mid outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (hpre : LoopSound ctx bound best mid)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound recSt out mid
      outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.receipt.prefix hpre, h.event, h.preserved⟩

/-- Changing the mutable entry workset does not affect a completed loop
outcome. -/
theorem LoopOutcome.reindexSet {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell tcell' : VSet n} {cursor : Option Nat}
    {bound : Key n} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell' cursor bound st out best outBest
      receiptTrail eventTrail r :=
  ⟨h.receipt.reindexSet, h.event, h.preserved⟩

/-- One successful cursor step preserves the coupled loop outcome. -/
theorem LoopOutcome.step {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level tv : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Option Int}
    (ha : After cursor tv)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell (some tv) bound st out
      best outBest receiptTrail eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest receiptTrail eventTrail r :=
  ⟨h.receipt.step ha, h.event, h.preserved⟩

/-- A coupled loop outcome can be rebased onto an entry trail that
agrees below the loop level. -/
theorem LoopOutcome.retrail {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel loopFuel level : Nat}
    {stem codes fs : List Nat} {rsLab rsPtn : Array Nat}
    {tc len numcells : Nat} {tcell : VSet n} {cursor : Option Nat} {bound : Key n}
    {st out : SearchSt n} {best outBest : Option (Key n)}
    {source dest eventTrail : FrameTrail} {r : Option Int}
    (htrail : TrailExt level dest source)
    (h : LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor bound st out best
      outBest source eventTrail r) :
    LoopOutcome G ctx tcLevel specFuel runFuel loopFuel level stem codes fs
      rsLab rsPtn tc len numcells tcell cursor bound st out best outBest
      dest eventTrail r :=
  ⟨h.receipt.retrail htrail, h.event, htrail.trans h.preserved⟩

/-- First-path exit bookkeeping preserves a corrected node outcome. -/
theorem NodeOutcome.firstFinish {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells size index : Nat}
    {cs fs : List Nat} {st out : SearchSt n} {best outBest : Option (Key n)}
    {receiptTrail eventTrail : FrameTrail} {r : Int}
    (hfuel : runFuel ≠ 0)
    (h : NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st out
      numcells best outBest receiptTrail eventTrail r) :
    NodeOutcome G ctx tcLevel specFuel runFuel level cs fs st
      (Nauty.firstFinish level size index out) numcells best outBest
      receiptTrail eventTrail r := by
  constructor
  · exact h.receipt.firstFinish hfuel
  · unfold Nauty.firstFinish
    split
    · exact h.event.setAllsame
    · exact h.event
  · exact h.preserved

/-- The first discrete leaf closes the corrected result package.  Its
generator store is still empty, so every return-frame stabilization
obligation is vacuous. -/
theorem FirstInv.terminalOutcome {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {cs : List Nat} {st : SearchSt n} {trail : FrameTrail}
    (hn0 : 0 < n) (hlevel : level = cs.length + 1)
    (h : FirstInv G ctx level cs numcells st trail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := cs ++ [rs.longcode]
    let out := firstPathNode ctx inf tcLevel (fuel + 1) level numcells st
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level cs full st
      out.2 numcells none (some (pathLeafKey ctx full rs.lab)) trail trail
      out.1 := by
  dsimp only
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let full := cs ++ [rs.longcode]
  let leaf := firstLeafSt ctx level numcells st
  have hstate := firstPath_discrete_state ctx inf tcLevel fuel level
    numcells st hnum
  have hbase := h.terminalReceipt
    (inf := inf) (tcLevel := tcLevel) (specFuel := specFuel)
    (fuel := fuel) hn0 hlevel hnum
  have hdepth : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take cs.length = cs := by
    simp only [full, List.take_left']
  have hempty : (firstterminal level leaf).genTrace = #[] := by
    rw [(firstterminal_store level leaf).1]
    exact h.genEmpty
  constructor
  · exact hbase.1
  · rw [hstate]
    have hrun := hbase.2
    rw [hstate] at hrun
    apply EventOut.ofRun hrun hdepth hstem (by omega)
    · omega
    · rw [(firstterminal_state level leaf).2.2.2.2]
      omega
    · exact ReturnStab.empty hempty
    · apply RefTrail.ofCurrent hrun.trailOk h.frameSize
      · rw [firstterminal_firstlab, (firstterminal_state level leaf).1]
      · rw [firstterminal_canonlab, (firstterminal_state level leaf).1]
  · exact TrailExt.refl level trail

set_option maxHeartbeats 800000 in
/-- A coupled child-loop outcome supplies the complete outcome of a
non-discrete first-path node. -/
theorem firstPath_internal_outcome {G : Colored n k} (ctx : Ctx n)
    (inf tcLevel specFuel fuel level numcells tail : Nat)
    (cs fs : List Nat) (st : SearchSt n) (best outBest : Option (Key n))
    (trail outTrail : FrameTrail)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells ≠ n)
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
    let pre0 : SearchSt n := { st with
      lab := rs.lab
      ptn := rs.ptn
      active := rs.active
      firstcode := st.firstcode.set! level rs.longcode
      firsttc := st.firsttc.set! level (Int.ofNat mt.1)
      numnodes := st.numnodes + 1
      tctotal := st.tctotal + mt.2.2 }
    let pre := if pre0.noncheaplevel ≥ level ∧
        ¬ cheapautom pre0.ptn level n then
      { pre0 with noncheaplevel := level + 1 }
    else pre0
    let L := firstChildLoop ctx inf tcLevel fuel (n + 1) level
      rs.numcells mt.1 ((mt.2.1.nextElem none).getD 0)
      (mt.2.1.nextElem none) mt.2.1 0 pre
    LoopOutcome G ctx tcLevel specFuel fuel (n + 1) level cs
      (cs ++ [rs.longcode]) fs rs.lab rs.ptn mt.1 mt.2.2 rs.numcells
      mt.2.1 none
      (nodeKey ctx tcLevel (specFuel + 1) level cs st numcells)
      pre L.2.2 best outBest trail outTrail L.1 →
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level cs fs st
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best outBest trail outTrail
      (firstPathNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
  dsimp only
  intro hloop
  rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
  generalize hL : firstChildLoop ctx inf tcLevel fuel (n + 1)
      level _ _ _ _ _ _ _ = L at hloop ⊢
  rcases L with ⟨r, index, out⟩
  cases r with
  | none =>
      have hnode := hloop.toNodeNone (nodeRunFuel := fuel + 1)
        rfl hchildren hlen
        (by simp only [cursorRank]; omega)
      exact hnode.firstFinish (by omega)
  | some r =>
      exact hloop.toNodeSome (nodeRunFuel := fuel + 1) rfl

/-- Once the imperative prefix exposes an off-path child loop, its
coupled outcome constructs the corresponding node outcome. -/
theorem otherNode_outcome {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level nodeNumcells loopNumcells tail : Nat}
    {nodeCs loopCs fs : List Nat} {nodeSt loopSt : SearchSt n}
    {rsLab rsPtn : Array Nat} {tc len : Nat} {tcell : VSet n}
    {best outBest : Option (Key n)} {trail outTrail : FrameTrail}
    {L : Option Int × SearchSt n}
    (hchildren : nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells =
      keysMax
        (sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
          loopNumcells 0)
        ((List.range tail).map fun o =>
          sweepKey ctx tcLevel specFuel level loopCs rsLab rsPtn tc
            loopNumcells (o + 1)))
    (hlen : len = tail + 1)
    (hstate : otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt =
      match L.1 with
      | some r => (r, L.2)
      | none => (Int.ofNat level - 1, L.2))
    (hloop : LoopOutcome G ctx tcLevel specFuel fuel (n + 1) level
      nodeCs loopCs fs rsLab rsPtn tc len loopNumcells tcell none
      (nodeKey ctx tcLevel (specFuel + 1) level nodeCs nodeSt
        nodeNumcells)
      loopSt L.2 best outBest trail outTrail L.1) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level nodeCs fs
      nodeSt (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).2
      nodeNumcells best outBest trail outTrail
      (otherNode ctx inf tcLevel (fuel + 1) level nodeNumcells
        nodeSt).1 := by
  rw [hstate]
  rcases L with ⟨r, out⟩
  cases r with
  | none =>
      exact hloop.toNodeNone (nodeRunFuel := fuel + 1) rfl hchildren hlen
        (by simp only [cursorRank]; omega)
  | some r =>
      exact hloop.toNodeSome (nodeRunFuel := fuel + 1) rfl

end Hex.GraphIso.Nauty

/-!
The live hypotheses shared by the corrected mutual search induction.

These clauses deliberately describe a state at which search may continue.
GCA ordering is not a result-side invariant: the first-child loop raises
`gcaFirst` before an early unwind, so a returned state need not satisfy it.
-/

namespace Hex.GraphIso.Nauty

/-- Every vertex recorded as fixed occupies a singleton cell of the
current partition.  This is the executable path fact that makes erasing a
completed child's temporary fixed vertex restore its parent set exactly. -/
@[expose] def FixedCells (level : Nat) (st : SearchSt n) : Prop :=
  ∀ v, v < n → st.fixedpts.mem v = true →
    ∃ q, q < n ∧ st.lab[q]! = v ∧ IsCell st.ptn level q 1

namespace FixedCells

/-- The initial search has no fixed vertices. -/
theorem root {G : Colored n k} :
    FixedCells 1
      (rootSt n (initialPartition G).1 (initialPartition G).2) := by
  intro v hv hm
  simp [rootSt] at hm

/-- A vertex in a non-singleton target cell is not already fixed. -/
theorem fresh {level tc len o : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hok : LabOk st.lab n)
    (hinj : LabInj st.lab n) (hsize : st.lab.size = n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    st.fixedpts.mem st.lab[tc + o]! = false := by
  rcases hm : st.fixedpts.mem st.lab[tc + o]! with _ | _
  · rfl
  · have hv : st.lab[tc + o]! < n := by
      exact hok (tc + o) (by omega)
    obtain ⟨q, hq, hqv, hsingle⟩ := h _ hv hm
    have heq : q = tc + o := by
      apply LabInj.eq_of_getElem! hinj hq (by omega)
      exact hqv
    subst q
    rcases isCell_disj_or_eq hsingle hcell with heq | hleft | hright
    · omega
    · omega
    · omega

/-- Reordering vertices within unchanged cells preserves fixed
singletons. -/
theorem ofCellsPerm {level : Nat} {st out : SearchSt n}
    (h : FixedCells level st) (hfixed : out.fixedpts = st.fixedpts)
    (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab) :
    FixedCells level out := by
  intro v hv hm
  rw [hfixed] at hm
  obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hm
  refine ⟨q, hq, ?_, ?_⟩
  · rw [← hqv]
    exact (cellsPerm_singleton hperm hsingle).symm
  · rw [hptn]
    exact hsingle

/-- A parent-level search effect preserves fixed singletons when it
preserves the fixed-point bitset. -/
theorem ofSearchOut {G : Colored n k} {level numcells : Nat}
    {st out : SearchSt n} (h : FixedCells level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    FixedCells level out :=
  h.ofCellsPerm hfixed (heffect.ptnEq hok hout) heffect.perm

/-- Refinement preserves every existing fixed singleton. -/
theorem refine {ctx : Ctx n} {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hsize : st.lab.size = n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    FixedCells level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro v hv hm
  obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hm
  refine ⟨q, hq, ?_, ?_⟩
  · exact (refine_fixes_singleton (by rw [hpsize]; exact Nat.le_refl _)
      (by rw [hsize, hpsize]) hend hsingle).trans hqv
  · exact isCell_refine_one (by rw [hpsize])
      (by rw [hsize, hpsize]) hend hsingle

/-- Individualizing a fresh target vertex adds exactly one fixed
singleton and preserves every older fixed singleton. -/
theorem breakout {level tc len o : Nat} {st : SearchSt n}
    (h : FixedCells level st) (hinj : LabInj st.lab n)
    (hsize : st.lab.size = n)
    (hpsize : st.ptn.size = n)
    (hcell : IsCell st.ptn level tc len) (hlen : 2 ≤ len)
    (hrange : tc + len ≤ n) (ho : o < len) :
    FixedCells (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  have hinjSize : LabInj st.lab st.lab.size := by
    rw [hsize]
    exact hinj
  intro v hv hm
  rw [VSet.mem_insert] at hm
  rcases (Bool.or_eq_true _ _).mp hm with hold | hnew
  · obtain ⟨q, hq, hqv, hsingle⟩ := h v hv hold
    have hne : q ≠ tc := by
      intro heq
      subst q
      rcases isCell_disj_or_eq hsingle hcell with heq | hleft | hright
      · omega
      · omega
      · omega
    have hout := singleton_outside_cell hsingle hcell hne ho
    refine ⟨q, hq, ?_, ?_⟩
    · exact (breakout_misses_singleton (n := n) (ptn := st.ptn)
        (level := level) hinjSize (by rw [hsize]; omega) hout).trans hqv
    · rw [breakout_ptn]
      exact isCell_set_miss hsingle hcell hlen
  · have heq : st.lab[tc + o]! = v :=
      beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hnew).1
    refine ⟨tc, by omega, ?_, ?_⟩
    · rw [breakout_at_target hinjSize (by rw [hsize]; omega), heq]
    · exact isCell_breakout_target (n := n) (lab := st.lab)
        (tv := st.lab[tc + o]!) (by rw [hpsize]; omega) hcell.2.1

end FixedCells

/-- Passing a fix test for a larger fixed set implies passing it for any
pointwise smaller set. -/
theorem fixTest_mono {small large fix : VSet n}
    (hsub : ∀ v, small.mem v = true → large.mem v = true)
    (hfix : large.subset fix = true) :
    small.subset fix = true :=
  VSet.subset_iff.mpr fun v hv => VSet.subset_iff.mp hfix v (hsub v hv)

/-- The bounded automorphism workspace is valid at the current frame for
every entry whose fixed set covers the current search path. -/
@[expose] def LocalAutos (ctx : Ctx n) (level : Nat) (st : SearchSt n) : Prop :=
  ∀ p ∈ st.autos.toList,
    st.fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2

namespace LocalAutos

/-- An empty workspace is locally valid. -/
theorem empty {ctx : Ctx n} {level : Nat} {st : SearchSt n}
    (h : st.autos = #[]) : LocalAutos ctx level st := by
  intro p hp
  rw [h] at hp
  simp at hp

/-- Cell stabilization is independent of the ordering chosen inside each
cell. -/
theorem reindexStab {ptn lab lab' gamma : Array Nat} {level n : Nat}
    (h : CellStab ptn level lab gamma)
    (hperm : cellsPerm ptn level lab lab')
    (hpsize : ptn.size = n) (hsize : lab.size = n)
    (hsize' : lab'.size = n) (hend : ptn[ptn.size - 1]! ≤ level) :
    CellStab ptn level lab' gamma := by
  apply cellStab_of_scatter hpsize hsize' hsize hend
      (cellsPerm_symm hperm)
      (cellsPerm_trans (cellsPerm_symm hperm) h)
  intro i hi
  rw [getElem!_map_of_lt _ _ (by rw [hsize]; exact hi)]

/-- A locally valid pair remains valid after reordering the frame within
its cells. -/
theorem reindexPair {ctx : Ctx n} {ptn lab lab' : Array Nat}
    {level : Nat} {fix mcr : VSet n}
    (h : PairOk ctx.g ptn lab level fix mcr)
    (hperm : cellsPerm ptn level lab lab')
    (hpsize : ptn.size = n) (hsize : lab.size = n)
    (hsize' : lab'.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    PairOk ctx.g ptn lab' level fix mcr := by
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfix, hstab, hlt⟩ := h v hv hmcr
  exact ⟨gamma, hcheck, hfix,
    reindexStab hstab hperm hpsize hsize hsize' hend, hlt⟩

/-- Local ledger validity transports across unchanged partition cells and
a within-cell labelling permutation. -/
theorem ofCellsPerm {ctx : Ctx n} {level : Nat} {st out : SearchSt n}
    (h : LocalAutos ctx level st) (hautos : out.autos = st.autos)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = n) (hsize : st.lab.size = n)
    (hsize' : out.lab.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    LocalAutos ctx level out := by
  intro p hp hfix
  rw [hautos] at hp
  rw [hfixed] at hfix
  have hpair := h p hp hfix
  rw [hptn]
  exact reindexPair hpair hperm hpsize hsize hsize' hend

/-- The conditional local ledger descends through one
individualization.  A pair applicable to the enlarged fixed set fixes the
selected vertex, exactly the premise needed by `cellStab_breakout`. -/
theorem breakout {ctx : Ctx n} {level tc len o : Nat} {st : SearchSt n}
    (h : LocalAutos ctx level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size) (hsize : st.lab.size = st.ptn.size)
    (hlab : LabOk st.lab n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    LocalAutos ctx (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  intro p hp hfix
  have hsub : ∀ v, st.fixedpts.mem v = true →
      (st.fixedpts.insert st.lab[tc + o]!).mem v = true := by
    intro v hv
    exact VSet.mem_insert_mono _ _ hv
  have hparent := fixTest_mono hsub hfix
  have hpair := h p hp hparent
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hpair v hv hmcr
  have hselected : p.1.mem st.lab[tc + o]! = true :=
    VSet.subset_iff.mp hfix _
      (VSet.mem_insert_self _ (hlab _ (by rw [hsize]; omega)))
  have hselectedBound : st.lab[tc + o]! < n :=
    hlab _ (by rw [hsize]; omega)
  exact ⟨gamma, hcheck, hfixes,
    cellStab_breakout (n := n) hstab hcell hrange hsize ho hlen hend hvals
      (hfixes _ hselectedBound hselected), hlt⟩

/-- The conditional local ledger is preserved by equitable refinement. -/
theorem refine {ctx : Ctx n} {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : LocalAutos ctx level st) (hgsz : ctx.g.size = n)
    (hsize : st.lab.size = n) (hlab : LabOk st.lab n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    LocalAutos ctx level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro p hp hfix
  have hpair := h p hp hfix
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hpair v hv hmcr
  exact ⟨gamma, hcheck, hfixes,
    cellStab_refine (n := n) hstab hgsz hcheck hsize hlab
      hpsize hend hstarts, hlt⟩

end LocalAutos

/-- A root-stabilizing checked automorphism that fixes every vertex on the
current individualized path stabilizes the current partition.  Keeping the
root frame explicit lets the existing root autos ledger supply the same
witness at every pruning site. -/
@[expose] def PathStab (ctx : Ctx n) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt n) : Prop :=
  ∀ gamma, checkAutom ctx.g gamma = true →
    CellStab rootPtn 1 rootLab gamma →
    (∀ u, u < n → st.fixedpts.mem u = true → gamma[u]! = u) →
    CellStab st.ptn level st.lab gamma

namespace PathStab

/-- A frame is its own path-stabilization seed. -/
theorem same {ctx : Ctx n} {st : SearchSt n} :
    PathStab ctx st.ptn st.lab 1 st := by
  intro gamma _ hstab _
  exact hstab

/-- Reordering the current labelling within unchanged cells preserves path
stabilization. -/
theorem ofCellsPerm {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st out : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts) (hptn : out.ptn = st.ptn)
    (hperm : cellsPerm st.ptn level st.lab out.lab)
    (hpsize : st.ptn.size = n) (hsize : st.lab.size = n)
    (hsize' : out.lab.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  intro gamma hcheck hroot hfix
  rw [hfixed] at hfix
  rw [hptn]
  exact LocalAutos.reindexStab (h gamma hcheck hroot hfix) hperm
    hpsize hsize hsize' hend

/-- A parent-level search effect preserves path stabilization when it
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt n}
   
    (h : PathStab ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level out := by
  exact h.ofCellsPerm hfixed (heffect.ptnEq hok hout) heffect.perm
    hok.ptnSize hok.labSize hout.labSize hend

/-- Equitable refinement preserves path stabilization. -/
theorem refine {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {active : VSet n} {numcells : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hgsz : ctx.g.size = n)
    (hsize : st.lab.size = n) (hlab : LabOk st.lab n)
    (hpsize : st.ptn.size = n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level) :
    PathStab ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  intro gamma hcheck hroot hfix
  exact cellStab_refine (n := n)
    (h gamma hcheck hroot hfix) hgsz hcheck hsize hlab hpsize
    hend hstarts

/-- Individualization extends path stabilization because an automorphism
fixing the enlarged path fixes the selected target vertex. -/
theorem breakout {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level tc len o : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hcell : IsCell st.ptn level tc len)
    (hrange : tc + len ≤ st.ptn.size)
    (hsize : st.lab.size = st.ptn.size) (hlab : LabOk st.lab n)
    (ho : o < len) (hlen : 2 ≤ len)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    (hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1) :
    PathStab ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + o]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + o]! } := by
  intro gamma hcheck hroot hfix
  have hparent : ∀ u, u < n → st.fixedpts.mem u = true →
      gamma[u]! = u := by
    intro u hu hm
    exact hfix u hu (VSet.mem_insert_mono _ _ hm)
  have hselected : gamma[st.lab[tc + o]!]! = st.lab[tc + o]! := by
    exact hfix _ (hlab _ (by rw [hsize]; omega))
      (VSet.mem_insert_self _ (hlab _ (by rw [hsize]; omega)))
  exact cellStab_breakout (n := n) (h gamma hcheck hroot hparent) hcell hrange
    hsize ho hlen hend hvals hselected

/-- The root autos ledger and path stabilization reconstruct the
conditional ledger consumed by the two pruning filters. -/
theorem toLocal {ctx : Ctx n} {rootPtn rootLab : Array Nat}
    {level : Nat} {st : SearchSt n}
    (h : PathStab ctx rootPtn rootLab level st)
    (hroot : AutosOk ctx.g rootPtn rootLab 1 st.autos) :
    LocalAutos ctx level st := by
  intro p hp hfix v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ :=
    hroot p hp v hv hmcr
  refine ⟨gamma, hcheck, hfixes, ?_, hlt⟩
  apply h gamma hcheck hstab
  intro u hu hmem
  exact hfixes u hu (VSet.subset_iff.mp hfix _ hmem)

end PathStab

/-! # Fixed-point frame equations -/

theorem pushAuto_fixedpts (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).fixedpts = st.fixedpts := by
  rw [pushAuto]
  split <;> rfl

/-- Leaf processing never changes the individualized path. -/
theorem processnode_fixedpts (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.fixedpts = st.fixedpts := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.fixedpts),
    pushAuto_fixedpts, ite_self]

/-- Comparison preparation never changes the individualized path. -/
theorem otherNodePrep_fixedpts (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).fixedpts = st.fixedpts := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.fixedpts, ite_self]

/-- Recovery never changes the individualized path. -/
theorem recover_fixedpts (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).fixedpts = st.fixedpts := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.fixedpts, ite_self]

/-- First-leaf installation never changes the individualized path. -/
theorem firstterminal_fixedpts (level : Nat) (st : SearchSt n) :
    (firstterminal level st).fixedpts = st.fixedpts := by
  rw [firstterminal]
  rfl

/-- First-path sweep cleanup never changes the individualized path. -/
theorem firstFinish_fixedpts (level size index : Nat) (st : SearchSt n) :
    (firstFinish level size index st).fixedpts = st.fixedpts := by
  rw [firstFinish]
  split <;> rfl

/-- The two path facts threaded only by the corrected mutual induction:
fixed vertices are singleton cells, and root-valid automorphisms fixing
them stabilize the current cells. -/
structure PathOk (ctx : Ctx n) (rootPtn rootLab : Array Nat)
    (level : Nat) (st : SearchSt n) : Prop where
  fixed : FixedCells level st
  stab : PathStab ctx rootPtn rootLab level st

namespace PathOk

/-- The nonempty root seeds both path facts. -/
theorem root {G : Colored n k} :
    PathOk { g := rowsOf G }
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1
      (rootSt n (initialPartition G).1 (initialPartition G).2) := by
  constructor
  · exact FixedCells.root
  · simpa only [rootSt] using
      (PathStab.same (ctx := { g := rowsOf G })
        (st := rootSt n (initialPartition G).1
          (initialPartition G).2))

/-- Node-entry refinement preserves both path facts. -/
theorem refine {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level : Nat} {active : VSet n} {numcells : Nat}
    {st : SearchSt n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hgsz : ctx.g.size = n)
    (hok : SearchOk G level numcells st)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ st.ptn[v - 1]! ≤ level)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab level
      { st with
        lab := (Nauty.refine ctx level st.lab st.ptn active numcells).lab
        ptn := (Nauty.refine ctx level st.lab st.ptn active numcells).ptn
        active := (Nauty.refine ctx level st.lab st.ptn active numcells).active } := by
  have hend := searchOk_end hn0 hok hlevel
  have hlab : LabOk st.lab n :=
    labOk_of_reach hok.labSize hok.reach
  constructor
  · exact h.fixed.refine hok.labSize hok.ptnSize hend
  · exact h.stab.refine hgsz hok.labSize hlab hok.ptnSize
      hend hstarts

/-- A loop child extends both path facts by its selected fresh vertex. -/
theorem breakout {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab rsLab rsPtn : Array Nat}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {currentOffset : Nat}
    {codes bs fs : List Nat} {cursor : Option Nat}
    {base st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hcurrent : currentOffset < len)
    (h : PathOk ctx rootPtn rootLab level st) :
    PathOk ctx rootPtn rootLab (level + 1)
      { st with
        lab := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (Nauty.breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! } := by
  have hok := hinv.run.searchOk
  have hend := searchOk_end hinv.nonempty hok hinv.positive
  have hlab : LabOk st.lab n :=
    labOk_of_reach hok.labSize hok.reach
  have hinj : LabInj st.lab n :=
    labInj_of_reach hok.labSize hinv.nonempty hok.reach
  have hvals : ∀ q : Nat, st.ptn[q]! ≠ level + 1 := by
    intro q heq
    rw [hinv.ptnEq] at heq
    rcases hinv.values q with hle | hinf
    · omega
    · have hbound := hinv.fuelBound
      omega
  constructor
  · exact h.fixed.breakout hinj hok.labSize hok.ptnSize
      hinv.currentCell hinv.lenTwo hinv.range hcurrent
  · exact h.stab.breakout hinv.currentCell
      (by rw [hok.ptnSize]; exact hinv.range)
      (hok.labSize.trans hok.ptnSize.symm) hlab hcurrent hinv.lenTwo
      hend hvals

/-- Recovered parent state preserves both path facts once child cleanup
restores the parent's fixed-point set. -/
theorem ofSearchOut {G : Colored n k} {ctx : Ctx n}
    {rootPtn rootLab : Array Nat} {level numcells : Nat}
    {st out : SearchSt n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (h : PathOk ctx rootPtn rootLab level st)
    (hfixed : out.fixedpts = st.fixedpts)
    (hok : SearchOk G level numcells st)
    (hout : SearchOk G level numcells out)
    (heffect : SearchOut G level level st out) :
    PathOk ctx rootPtn rootLab level out := by
  constructor
  · exact h.fixed.ofSearchOut hfixed hok hout heffect
  · exact h.stab.ofSearchOut hfixed hok hout heffect
      (searchOk_end hn0 hok hlevel)

/-- The path facts and root ledger supply the exact local ledger needed
by a pruning filter. -/
theorem autos {G : Colored n k} {ctx : Ctx n}
    {level numcells tcLevel : Nat} {cs bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hrun : RunInv G ctx tcLevel level cs bs fs numcells st best trail) :
    LocalAutos ctx level st :=
  hpath.stab.toLocal hrun.autosOk

/-- A root-valid pair whose `fix` contains the individualized path is
valid at the current search frame, even when that pair was admitted by a
deeper result state rather than being present on entry. -/
theorem pair {G : Colored n k} {ctx : Ctx n}
    {level : Nat} {st : SearchSt n} {fix mcr : VSet n}
    (hpath : PathOk ctx
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (hroot : PairOk ctx.g
      (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 1 fix mcr)
    (hcovers : ∀ v, v < n → st.fixedpts.mem v = true →
      fix.mem v = true) :
    PairOk ctx.g st.ptn st.lab level fix mcr := by
  intro v hv hmcr
  obtain ⟨gamma, hcheck, hfixes, hstab, hlt⟩ := hroot v hv hmcr
  refine ⟨gamma, hcheck, hfixes, ?_, hlt⟩
  apply hpath.stab gamma hcheck hstab
  intro u hu hfixed
  exact hfixes u hu (hcovers u hu hfixed)

end PathOk

/-- Reference history, ordered live guides, and stabilization of every
ancestor frame to which the current node may return. -/
structure Live (ctx : Ctx n) (level : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop where
  history : RefTrail ctx level st trail
  order : st.gcaFirst ≤ st.gcaCanon
  stable : ReturnStab trail (Int.ofNat st.gcaFirst) st

namespace Live

/-- `Live` depends only on the two reference controls and labellings and
on the recorded-generator store. -/
theorem stateEq {ctx : Ctx n} {level : Nat} {st st' : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (hfirstGca : st'.gcaFirst = st.gcaFirst)
    (hfirst : st'.firstlab = st.firstlab)
    (hcanonGca : st'.gcaCanon = st.gcaCanon)
    (hcanon : st'.canonlab = st.canonlab)
    (hgen : st'.genTrace = st.genTrace) :
    Live ctx level st' trail := by
  constructor
  · exact h.history.stateEq hfirstGca hfirst hcanonGca hcanon
  · rw [hfirstGca, hcanonGca]
    exact h.order
  · rw [hfirstGca]
    exact h.stable.ofGenTraceEq hgen

/-- Target-cell accounting changes no live field. -/
theorem setTctotal {ctx : Ctx n} {level value : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with tctotal := value } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Parking the cheap-automorphism boundary changes no live field. -/
theorem park {ctx : Ctx n} {level boundary : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with noncheaplevel := boundary } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Fixed-point cleanup changes no live field. -/
theorem setFixed {ctx : Ctx n} {level : Nat} {fixedpts : VSet n} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with fixedpts := fixedpts } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Clearing the one-shot short-prune flag changes no live field. -/
theorem clearShort {ctx : Ctx n} {level : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level { st with needshortprune := false } trail :=
  h.stateEq rfl rfl rfl rfl rfl

/-- Refinement and the off-path comparison step preserve the complete live
package. -/
theorem otherLeaf {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail) :
    Live ctx level (otherLeafSt ctx level numcells st) trail :=
  ⟨h.history.otherLeaf, RefTrail.otherLeaf_order h.order, by
    simpa only [RefTrail.otherLeaf_gcaFirst] using h.stable.otherLeaf⟩

/-- A leaf event preserves reference history and live GCA ordering.  Its
return-indexed generator stabilization is supplied separately by the
admission classifier. -/
theorem processnode {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {trail : FrameTrail} (h : Live ctx level st trail)
    (htrail : TrailOk ctx level st trail) (hfirst : st.gcaFirst ≤ level) :
    RefTrail ctx level (Nauty.processnode ctx level numcells st).2 trail ∧
      (Nauty.processnode ctx level numcells st).2.gcaFirst ≤
        (Nauty.processnode ctx level numcells st).2.gcaCanon :=
  ⟨h.history.processnode htrail,
    RefTrail.processnode_order h.order hfirst⟩

/-- The explicit pair admitted by a code-two row tie is valid at its
canonical return frame, not merely at the root ledger.  This is the local
fact consumed when the one-shot short-prune flag reaches that frame. -/
theorem rowTiePair {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    {entry : TrailEntry}
    (hn0 : 0 < n)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hbelow : st.gcaCanon < level)
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hentry : trail st.gcaCanon = some entry) :
    PairOk ctx.g entry.frame.rsPtn entry.frame.rsLab st.gcaCanon
      (fmperm (canonScatter n st.canonlab st.lab) n).1
      (fmperm (canonScatter n st.canonlab st.lab) n).2 := by
  have hcanonOk := labOk_of_reach hprep.leafRefs.canonSize
    hprep.leafRefs.canonReach
  have hinj := labInj_of_reach hprep.leafRefs.canonSize hn0
    hprep.leafRefs.canonReach
  have hmap : ∀ i, i < n →
      (canonScatter n st.canonlab st.lab)[st.canonlab[i]!]! =
        st.lab[i]! := by
    intro i hi
    rw [canonScatter_eq_firstScatter]
    apply firstScatter_get
      (fun _ _ ha hb hab => hinj.eq_of_getElem! (by omega) (by omega) hab)
      (fun j hj => hcanonOk j (by
        rw [hprep.leafRefs.canonSize]
        omega))
    omega
  have hcheck : checkAutom ctx.g
      (canonScatter n st.canonlab st.lab) = true := by
    apply checkAutom_scatter_of_leafRows_eq
      (by
        rw [canonScatter_eq_firstScatter]
        exact firstScatter_size n st.canonlab st.lab)
      hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      (fun i hi => hmap i (by omega))
      (rows_eq_of_testcanlab_tie hprep.canongInv htie)
  have hstab : CellStab entry.frame.rsPtn st.gcaCanon
      entry.frame.rsLab (canonScatter n st.canonlab st.lab) := by
    apply hlive.history.canonStab hprep.trailOk
      hprep.leafRefs.canonSize hbelow hmap st.gcaCanon entry
    · exact Int.le_refl _
    · exact hentry
  have hframeSize := hlive.history.frameSize st.gcaCanon entry hbelow hentry
  have hframeReach := hprep.trailOk.reach st.gcaCanon entry hbelow hentry
  have hptnSize := hprep.trailOk.ptnSize st.gcaCanon entry hbelow hentry
  have hend := hprep.trailOk.endClosed st.gcaCanon entry hbelow hentry
  have hframePerm :
      (segN entry.frame.rsLab 0 n).Perm (segN st.lab 0 n) := by
    apply cellsPerm_segN_perm hframeReach
    · rw [hptnSize]
      exact Nat.le_refl _
    · exact hend
    · simpa only [hptnSize] using hend
  have hframeOk : LabOk entry.frame.rsLab n := by
    apply labOk_of_perm hframePerm
      (labOk_of_reach hprep.searchOk.labSize hprep.searchOk.reach)
      hprep.searchOk.labSize hframeSize
  apply pairOk_fmperm
    hframeOk hframeSize hptnSize hend hcheck hstab

end Live

namespace RunPrep

/-- Workspace capacity makes the code-two pair the exact final entry read
by `shortprune`, including the full-workspace overwrite case. -/
theorem rowTieBack {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hcc : st.compCanon = 0) (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0) :
    (processnode ctx level numcells st).2.autos.back? = some
      (fmperm (canonScatter n st.canonlab st.lab) n) := by
  rw [processnode_rowTie_autos hef hnc hcc hge htie]
  exact pushAuto_back h.workspace.1

end RunPrep

/-- The live state of an off-path sweep.  `gcaFirst` stays strictly above
the divergence ancestor, so a child push introduces no new stabilization
obligation at the current frame. -/
structure OtherLive (ctx : Ctx n) (level : Nat) (st : SearchSt n)
    (trail : FrameTrail) : Prop extends Live ctx level st trail where
  firstBelow : st.gcaFirst < level

/-- The live state of a first-path sweep.  Once generators exist, the
guiding child has already been absorbed, and every recorded generator
stabilizes this frozen frame; before that point the store is empty and the
same clause is vacuous. -/
structure FirstLive (ctx : Ctx n) (level : Nat) (st : SearchSt n)
    (trail : FrameTrail) (rsLab rsPtn : Array Nat) : Prop
    extends Live ctx level st trail where
  frameStab : ∀ γ ∈ st.genTrace.toList,
    CellStab rsPtn level rsLab γ

namespace OtherOutcome

/-- Cleaning and recovering a completed off-path child reconstructs both
the parent's stable run invariant and its off-path live package. -/
theorem recover {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel childNumcells numcells level inf : Nat} {fixedpts : VSet n}
    {codes fs : List Nat} {child out : SearchSt n}
    {best outBest : Option (Key n)} {receiptTrail eventTrail : FrameTrail}
    {r : Int}
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out childNumcells best outBest receiptTrail eventTrail r)
    (hreturn : r = Int.ofNat level) (hpath : codes.length = level)
    (hlevel : 1 ≤ level) (hinf : level < inf)
    (hfirst : child.gcaFirst < level)
    (hok : SearchOk G level numcells
      (Nauty.recover n inf level { out with fixedpts := fixedpts })) :
    ∃ bs,
      RunInv G ctx tcLevel level codes bs fs numcells
          (Nauty.recover n inf level { out with fixedpts := fixedpts })
          outBest eventTrail ∧
        OtherLive ctx level
          (Nauty.recover n inf level { out with fixedpts := fixedpts })
          eventTrail := by
  have hfirstOut : out.gcaFirst < level := by
    rw [h.firstGuide]
    exact hfirst
  have hfirstClean : ({ out with fixedpts := fixedpts } : SearchSt n).gcaFirst ≤
      level := Nat.le_of_lt hfirstOut
  obtain ⟨bs, hrun, hstable, hhistory⟩ :=
    h.node.event.setFixed fixedpts |>.recoverRun hreturn hpath hlevel hinf
      hfirstClean hok
  refine ⟨bs, hrun, ?_⟩
  constructor
  · constructor
    · exact hhistory
    · exact RefTrail.recover_order (by simpa only using h.order)
        hfirstClean
    · exact hstable
  · rw [(recover_frames n inf level
      { out with fixedpts := fixedpts }).2.2.2.2.2.2.1]
    exact hfirstOut

/-- Resolving a returning off-path child advances the evolving sweep.
The impossible orbit-return arm is discharged by the strict first-guide
bound, so no current-child `cosetindex` equation is needed. -/
theorem cover {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len : Nat} {tcell : VSet n} {tv offset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st child out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      child out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (htv : rsLab[tc + offset]! = tv)
    (hfirst : child.gcaFirst < level)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes child
          (numcells + 1)) :
    SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest := by
  rcases h.node.parentReturn hfuel hstay with hfull |
      ⟨payload, hloc, _⟩
  · exact hinv.cover.advanceKey hnext hfull heq
  · apply hinv.cover.offPathUnwind
      (h.node.receipt.sound hfuel).grows hnext hloc
      (FrameTrail.push_self trail level _) hoffset htv
    · rw [h.firstGuide]
      exact hfirst
    · exact hinv.frozenLabSize
    · rw [← hinv.baseLab, hinv.baseOk.labSize]
      exact labInj_of_reach hinv.baseOk.labSize hinv.nonempty
        hinv.baseOk.reach
    · exact hinv.range

/-- After recovery, the first guide remains strictly older and the
canonical guide names either an earlier covered child or the child just
absorbed.  Thus both current-frame reference obligations are restored. -/
theorem refs {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset inf : Nat} {tcell fixedpts : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hcover : SweepCover ctx tcLevel specFuel level codes rsLab rsPtn tc len
      numcells tcell (some tv) outBest)
    (hfuel : runFuel ≠ 0)
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv) :
    FrameRefs ctx tcLevel specFuel level codes rsLab rsPtn tc len numcells
      (Nauty.recover n inf level { out with fixedpts := fixedpts })
      outBest := by
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
  let cleaned : SearchSt n := { out with fixedpts := fixedpts }
  have hinc : IncGrows best outBest :=
    (h.node.receipt.sound hfuel).grows
  constructor
  · intro heq
    have hfirstRec :=
      (recover_frames n inf level cleaned).2.2.2.2.2.2.1
    have hfirstChild : child.gcaFirst = st.gcaFirst := rfl
    have hfirstOut : out.gcaFirst = st.gcaFirst := by
      exact h.firstGuide.trans hfirstChild
    rw [hfirstRec] at heq
    change out.gcaFirst = level at heq
    rw [hfirstOut] at heq
    exact (Nat.ne_of_lt hlive.firstBelow heq).elim
  · intro heq
    have hcanonRec := recover_gcaCanon n inf level cleaned
    have hcanonLab := (recover_frames n inf level cleaned).1
    rcases h.canonGuide with hold | hnew
    · have hcanonChild : child.gcaCanon = st.gcaCanon := rfl
      have hcanonOut : out.gcaCanon = st.gcaCanon :=
        hold.1.trans hcanonChild
      have hcanonEq : st.gcaCanon = level := by
        rw [hcanonRec] at heq
        change (if level < out.gcaCanon then level else out.gcaCanon) =
          level at heq
        rw [hcanonOut] at heq
        rw [ite_eq_right (Nat.not_lt_of_ge hinv.run.canonBound)] at heq
        exact heq
      obtain ⟨o, ho, hdone, hatRef, hperm⟩ :=
        (hinv.refs.grow hinc).canon hcanonEq
      refine ⟨o, ho, hdone, ?_, ?_⟩
      · rw [hcanonLab]
        change out.canonlab[tc]! = rsLab[tc + o]!
        rw [hold.2]
        exact hatRef
      · rw [hcanonLab]
        change cellsPerm rsPtn level rsLab out.canonlab
        rw [hold.2]
        exact hperm
    · have hmem : tcell.mem rsLab[tc + offset]! = true := by
        rw [htv]
        exact VSet.nextElem_mem hnext
      have hdone : ChildDone ctx tcLevel specFuel level codes rsLab rsPtn tc
          numcells outBest offset :=
        hcover.past offset hoffset hmem (by
          simp only [After, htv]
          omega)
      have hstSize : st.lab.size = n := by
        exact hinv.run.searchOk.labSize
      have hstPtnSize : st.ptn.size = n := by
        exact hinv.run.searchOk.ptnSize
      have hcurrentPos : tc + currentOffset < st.lab.size := by
        rw [hstSize]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hcurrent tc)
          hinv.range
      have htcPtn : tc < st.ptn.size := by
        rw [hstPtnSize]
        exact Nat.lt_of_lt_of_le (by omega : tc < tc + len) hinv.range
      have hrangePtn : tc + len ≤ st.ptn.size := by
        rw [hstPtnSize]
        exact hinv.range
      have hstInj : LabInj st.lab st.lab.size := by
        rw [hinv.run.searchOk.labSize]
        exact labInj_of_reach hinv.run.searchOk.labSize hinv.nonempty
          hinv.run.searchOk.reach
      have hchildAt : child.lab[tc]! = tv := by
        change (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1[tc]! = tv
        rw [breakout_at_target hstInj hcurrentPos, hat]
      have hchildPtn : child.ptn = st.ptn.set! tc (level + 1) := by
        exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!
      have hchildCell : IsCell child.ptn (level + 1) tc 1 := by
        rw [hchildPtn]
        exact isCell_breakout_target (n := n) (lab := st.lab)
          (tv := st.lab[tc + currentOffset]!) htcPtn
          hinv.currentCell.2.1
      have houtAt : out.canonlab[tc]! = tv := by
        rw [← hchildAt]
        exact (cellsPerm_singleton hnew.2 hchildCell).symm
      have hchildOk : SearchOk G (level + 1) (numcells + 1) child := by
        apply breakout_searchOk hinv.nonempty hinv.run.searchOk hinv.positive
          hinv.currentCell hinv.lenTwo
          hinv.range hcurrent
        · rfl
        · exact hchildPtn
        · rfl
      have hfine : cellsPerm st.ptn level child.lab out.canonlab := by
        apply cellsPerm_coarsen (ptnF := child.ptn) (levF := level + 1)
        · rw [hchildPtn, Array.size_set!]
        · exact hchildOk.labSize.trans hchildOk.ptnSize.symm
        · rw [h.node.event.canonSize, hchildOk.ptnSize]
        · exact hnew.2
        · exact searchOk_end hinv.nonempty hchildOk (by omega)
        · exact searchOk_end hinv.nonempty hinv.run.searchOk hinv.positive
        · intro q hq
          rw [hchildPtn]
          rcases Decidable.em (tc = q) with rfl | hne
          · rw [Array.getElem!_set!_self _ _ _ htcPtn]
            exact Nat.le_refl _
          · rw [Array.getElem!_set!_ne _ _ _ _ hne]
            omega
      have hbreak : cellsPerm st.ptn level st.lab child.lab := by
        change cellsPerm st.ptn level st.lab
          (breakout n st.lab st.ptn (level + 1) tc
            st.lab[tc + currentOffset]!).1
        exact breakout_cellsPerm hinv.currentCell hrangePtn
          (by rw [hinv.run.searchOk.labSize, hinv.run.searchOk.ptnSize])
          hcurrent
      have hperm : cellsPerm rsPtn level rsLab out.canonlab := by
        rw [hinv.ptnEq] at hbreak hfine
        exact cellsPerm_trans hinv.labPerm (cellsPerm_trans hbreak hfine)
      refine ⟨offset, hoffset, hdone, ?_, ?_⟩
      · rw [hcanonLab]
        change out.canonlab[tc]! = rsLab[tc + offset]!
        rw [houtAt, htv]
      · rw [hcanonLab]
        exact hperm

/-- An ordinary off-path child return with no requested pruning rebuilds
the complete invariant for the recursive tail of the same sweep. -/
theorem next {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel runFuel level numcells tc len tv offset currentOffset inf : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st out : SearchSt n}
    {best outBest : Option (Key n)} {trail eventTrail : FrameTrail} {r : Int}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail)
    (h : OtherOutcome G ctx tcLevel specFuel runFuel (level + 1) codes fs
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out (numcells + 1) best outBest
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩)
      eventTrail r)
    (hout : SearchOut G level (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      out)
    (hinf : inf = n + 2) (hpath : codes.length = level)
    (hfuel : runFuel ≠ 0) (hstay : ¬(r < Int.ofNat level))
    (hnext : tcell.nextElem cursor = some tv)
    (hoffset : offset < len) (hcurrent : currentOffset < len)
    (htv : rsLab[tc + offset]! = tv)
    (hat : st.lab[tc + currentOffset]! = tv)
    (heq : ∀ o, o < len → rsLab[tc + o]! = tv →
      sweepKey ctx tcLevel specFuel level codes rsLab rsPtn tc numcells o =
        nodeKey ctx tcLevel specFuel (level + 1) codes
          { st with
            lab := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).1
            ptn := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.1
            active := (breakout n st.lab st.ptn (level + 1) tc
              st.lab[tc + currentOffset]!).2.2
            fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
          (numcells + 1))
    (hshort : out.needshortprune = false) :
    let cleaned : SearchSt n :=
      { out with fixedpts := out.fixedpts.erase tv }
    let recovered := Nauty.recover n inf level cleaned
    ∃ bs',
      LoopInv G ctx tcLevel specFuel level codes bs' fs numcells rsLab rsPtn
          tc len tcell (some tv) base recovered outBest eventTrail ∧
        OtherLive ctx level recovered eventTrail := by
  dsimp only
  let child : SearchSt n :=
    { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + currentOffset]!).2.2
      fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
  let cleaned : SearchSt n := { out with fixedpts := out.fixedpts.erase tv }
  let recovered := Nauty.recover n inf level cleaned
  have hreturn : r = Int.ofNat level := h.node.parentEq hfuel hstay
  have hfirst : child.gcaFirst < level := by
    change st.gcaFirst < level
    exact hlive.firstBelow
  have hcoverage := h.cover hinv hfuel hstay hnext hoffset htv hfirst heq
  have hrecovered := hinv.recoverChild hinf hcurrent hout
  have heffect : SearchOut G level level base recovered := by
    simpa only [cleaned, recovered, hat] using hrecovered.1
  have hok : SearchOk G level numcells recovered := by
    simpa only [cleaned, recovered, hat] using hrecovered.2
  have hinfLevel : level < inf := by
    rw [hinf]
    have hle : level ≤ n := Nat.le_trans hinv.run.searchOk.bc
      (bcount_le st.ptn level n)
    omega
  obtain ⟨bs', hrun, hlive'⟩ := h.recover hreturn hpath hinv.positive
    hinfLevel hfirst hok
  have hrefs := h.refs hinv hlive hcoverage hfuel hnext hoffset hcurrent
    htv hat (inf := inf) (fixedpts := out.fixedpts.erase tv)
  have hshort' : recovered.needshortprune = false := by
    unfold recovered cleaned
    rw [recover_needshortprune, hshort]
  refine ⟨bs', ?_, hlive'⟩
  exact {
    nonempty := hinv.nonempty
    positive := hinv.positive
    baseOk := hinv.baseOk
    run := hrun
    effect := heffect
    baseLab := hinv.baseLab
    basePtn := hinv.basePtn
    equitable := hinv.equitable
    cell := hinv.cell
    lenTwo := hinv.lenTwo
    range := hinv.range
    values := hinv.values
    members := hinv.members
    cover := hcoverage
    refs := hrefs
    shortClear := hshort'
    fuelBound := hinv.fuelBound }

end OtherOutcome

/-- The bookkeeping between an off-path node's refinement and its fresh
child sweep preserves the live package and the strict first-reference
bound. -/
theorem NodeInv.otherLive {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells len : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    let pre := otherLeafSt ctx level numcells st
    let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
    let start := if cheapautom base.ptn level n then base
      else { base with noncheaplevel := level + 1 }
    OtherLive ctx level start trail := by
  dsimp only
  let pre := otherLeafSt ctx level numcells st
  let base : SearchSt n := { pre with tctotal := pre.tctotal + len }
  have hpre : Live ctx level pre trail := by
    simpa only [pre] using hlive.otherLeaf (numcells := numcells)
  have hbase : Live ctx level base trail := by
    simpa only [base] using hpre.setTctotal (value := pre.tctotal + len)
  have hbelow : base.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  split
  · exact ⟨hbase, hbelow⟩
  · exact ⟨hbase.park, hbelow⟩

/-- A loop child inherits reference history and stabilization through its
live first-reference GCA.  The current frozen frame is required only when
that GCA is exactly the loop level. -/
theorem LoopInv.childLive {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) (offset currentOffset : Nat)
    (hframe : st.gcaFirst = level → ∀ γ ∈ st.genTrace.toList,
      CellStab rsPtn level rsLab γ) :
    Live ctx (level + 1)
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
  let entry : TrailEntry :=
    ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩
  have hstable : ReturnStab (trail.push level entry)
      (Int.ofNat st.gcaFirst) st := by
    apply hlive.stable.push
    intro hle γ hγ
    have hbound := hinv.run.firstBound
    have heq := Nat.le_antisymm hbound (Int.ofNat_le.mp hle)
    exact hframe heq γ hγ
  constructor
  · simpa only [entry] using
      RefTrail.LoopInv.childHistory hinv hlive.history offset currentOffset
  · simpa only using hlive.order
  · unfold ReturnStab at hstable ⊢
    exact hstable

/-- An off-path loop's strict first-reference bound discharges the only
new-frame premise of `childLive`. -/
theorem LoopInv.otherChildLive {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : OtherLive ctx level st trail) (offset currentOffset : Nat) :
    Live ctx (level + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc
          st.lab[tc + currentOffset]!).2.2
        fixedpts := st.fixedpts.insert st.lab[tc + currentOffset]! }
      (trail.push level
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) := by
  apply hinv.childLive hlive.toLive offset currentOffset
  intro heq
  exact (Nat.ne_of_lt hlive.firstBelow heq).elim

/-- A first-path loop carries stabilization of its frozen frame directly,
including the initial empty-store phase. -/
theorem LoopInv.firstChildLive {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n} {coset : Nat}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : FirstLive ctx level st trail rsLab rsPtn)
    (offset currentOffset : Nat) :
    Live ctx (level + 1)
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
        ⟨sweepFrame specFuel codes rsLab rsPtn tc numcells, offset⟩) :=
  hinv.childLive hlive.toLive offset currentOffset fun _ => hlive.frameStab

/-- A non-first leaf event whose branch does not append a generator
produces the complete result-side package.  The caller supplies the strict
return bound because `processnode` itself also has a non-unwinding result
at the current level. -/
theorem RunPrep.leafEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true)
    (hreturn : (processnode ctx level numcells st).1 ≤
      Int.ofNat level - 1)
    (hgen : (processnode ctx level numcells st).2.genTrace = st.genTrace)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn0 hsymm hloop
    hlevel hpath hbound hef hnc
  refine ⟨bs', ?_, hmax⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast
  · omega
  · have hs := hlive.stable.ofGenTraceEq hgen
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-one admission with a nonpositive incumbent comparison is a
fully verified generator event.  The semantic loop proof supplies the
nonpositivity premise from coverage of the guiding child. -/
theorem RunPrep.firstEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbelow : st.gcaFirst < level) (hnp : st.compCanon ≤ 0)
    (heq : (st.eqlevFirst == level) = true)
    (hsent : st.firstcode[level + 1]! = codeSentinel)
    (hnc : (numcells == n) = true)
    (hpass : isautom ctx
      (firstScatter n st.firstlab st.lab) = true)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    EventOut G ctx tcLevel stem fs
      (processnode ctx level numcells st).2 best trail
      (processnode ctx level numcells st).1 := by
  obtain ⟨hreturn, hcomp, heqCanon, hcode, hcanonlevel, hcanonlab,
      hcanong, hsamerows⟩ := processnode_auto heq hsent hnc hpass
  have hframes := processnode_frames ctx level numcells st
  have hgcaCanon := processnode_auto_gcaCanon heq hsent hnc hpass
  have hevent : RunEvent G ctx tcLevel level codes bs fs
      (processnode ctx level numcells st).2 best trail := by
    refine ⟨Or.inl ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hprep.bestCodes, ?_⟩
    · rw [hcomp]
      exact hnp
    · rw [hcomp, heqCanon, hcode, hcanonlevel]
      exact hprep.codeInv
    · rw [hframes.2.2.1, hframes.2.2.2.1]
      exact hprep.firstInv
    · rw [hcanong, hcanonlab, hsamerows]
      exact hprep.canongInv
    · exact hprep.leafRefs.processnodeGen hn0 hsymm hloop
        hprep.searchOk hprep.canongInv hprep.genTraceOk
    · exact hprep.autosOk.processnodeAuto hn0 hsymm hloop
        hprep.searchOk hprep.leafRefs heq hsent hnc hpass
    · exact hprep.workspace.processAuto heq hsent hnc hpass
    · exact hprep.cheap.processnode
    · exact hprep.leafRefs.processnode hprep.searchOk
    · apply hprep.guides.processnode (IncGrows.refl best)
        hframes.2.2.2.2.2.2.1 hframes.2.2.2.2.1
      intro _
      exact ⟨hgcaCanon, hcanonlab⟩
    · exact hprep.trailOk.processnode
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstPositive
    · rw [hgcaCanon]
      exact hprep.canonPositive
    · rw [hframes.2.2.2.2.2.2.1]
      exact hprep.firstBound
    · rw [hgcaCanon]
      exact hprep.canonBound
    · rw [hcanonlab]
      exact hprep.incumbent
  apply EventOut.intro level codes bs hevent hpath hstem hpast
  · rw [hreturn]
    exact Int.ofNat_le.mpr (Nat.le_of_lt hbelow)
  · have hs := hlive.history.processnodeFirstStab hn0
      hprep.trailOk hprep.leafRefs hlive.stable hbelow heq hsent hnc hpass
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A code-two row tie produces a verified event for either its canonical
return or its special first-ancestor orbit return. -/
theorem RunPrep.tiedEvent {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {stem codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hbound : st.noncheaplevel ≤ level)
    (hef : ¬((st.eqlevFirst == level) = true))
    (hnc : (numcells == n) = true) (hcc : st.compCanon = 0)
    (hge : ¬(level < st.canonlevel))
    (htie : (testcanlab ctx
      (updatecan ctx st.canong st.canonlab st.samerows) st.lab).1 = 0)
    (hcanonBelow : st.gcaCanon < level)
    (hprep : RunPrep G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ bs',
      EventOut G ctx tcLevel stem fs
          (processnode ctx level numcells st).2
          (some (incKey ctx bs'
            (processnode ctx level numcells st).2.canonlab)) trail
          (processnode ctx level numcells st).1 ∧
        incKey ctx bs' (processnode ctx level numcells st).2.canonlab =
          keyMax (incKey ctx bs st.canonlab)
            (pathLeafKey ctx codes st.lab) ∧
        some (incKey ctx bs'
          (processnode ctx level numcells st).2.canonlab) = best := by
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn0 hsymm hloop
    hlevel hpath hbound hef hnc
  have hcinv : CodeCmpInv n codes bs st.canoncode st.canonlevel
      st.eqlevCanon 0 := by
    simpa only [hcc] using hprep.codeInv
  have hlen : codes.length = bs.length := by
    have hle := codeInv_tied_le hcinv
    have hblen := hcinv.blen
    omega
  have hcodes : codes = bs := codeInv_eq_of_tied hcinv hlen
  have hrows : leafRows ctx st.canonlab = leafRows ctx st.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hkey : pathLeafKey ctx codes st.lab =
      incKey ctx bs st.canonlab := by
    unfold pathLeafKey incKey
    rw [hcodes, ← hrows]
  have houtBest : some (incKey ctx bs'
      (processnode ctx level numcells st).2.canonlab) = best := by
    rw [hmax, hkey, keyMax_eq_left (keyLe_refl _)]
    exact hprep.incumbent.symm
  have hreturns := (processnode_rowTie hef hnc hcc hge htie).1
  have hreturned : (processnode ctx level numcells st).1 ≤
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_le.mpr
        (Nat.le_trans hlive.order hprep.canonBound)
    · rw [hcanon]
      exact Int.ofNat_le.mpr hprep.canonBound
  refine ⟨bs', ?_, hmax, houtBest⟩
  apply EventOut.intro level codes bs' hevent hpath hstem hpast hreturned
  · have hs := hlive.history.processnodeTiedStab hn0 hprep.trailOk
      hprep.leafRefs hlive.order hlive.stable hcanonBelow hef hnc hcc hge
      htie
    rw [(processnode_frames ctx level numcells st).2.2.2.2.2.2.1]
    exact hs.lower (by omega)
  · exact (hlive.processnode hprep.trailOk hprep.firstBound).1

/-- A discrete code-one branch closes the complete node outcome.  Its
guide supplies the located unwind receipt, while `firstEvent` supplies
the result-state invariants. -/
theorem NodeInv.firstLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hnp : (otherLeafSt ctx level numcells st).compCanon ≤ 0)
    (heq : ((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true)
    (hsent : (otherLeafSt ctx level numcells st).firstcode[level + 1]! =
      codeSentinel)
    (hpass : isautom ctx (firstScatter n
      (otherLeafSt ctx level numcells st).firstlab
      (otherLeafSt ctx level numcells st).lab) = true)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
    ∃ target,
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 =
        Int.ofNat target ∧
      target < level ∧
      (target = (otherNode ctx inf tcLevel (fuel + 1) level numcells
          st).2.gcaFirst ∨
        target = (otherNode ctx inf tcLevel (fuel + 1) level numcells
          st).2.gcaCanon) ∧
      ∃ payload : Unwind ctx tcLevel target
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 best,
        payload.Located trail := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hbelow : leaf.gcaFirst < level := by
    change (otherLeafSt ctx level numcells st).gcaFirst < level
    rw [RefTrail.otherLeaf_gcaFirst]
    exact hnode.firstBelow
  have hevent : EventOut G ctx tcLevel codes fs
      (processnode ctx level n leaf).2 best trail
      (processnode ctx level n leaf).1 := by
    apply hprep.firstEvent hn0 hsymm hloop hfull hstem (by omega)
      hbelow hnp
      heq hsent (by simp) hpass hlive'
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_firstReceipt hnum hprep.guides hprep.trailOk
      hprep.firstPositive hbelow hgsz hprep.leafRefs.firstSize
      (isPerm_of_cellsReach hprep.leafRefs.firstSize hn0
        hprep.leafRefs.firstReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach)
      hsymm hloop heq hsent hpass
  have hreturn := (processnode_auto (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) heq hsent (by simp) hpass).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rw [hreturn]
    exact Int.ofNat_lt.mpr hbelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  obtain ⟨payload, hloc⟩ := hprep.guides.firstUnwind
    (numcells := n) hprep.trailOk
    hprep.firstPositive hbelow hgsz hprep.leafRefs.firstSize
    (isPerm_of_cellsReach hprep.leafRefs.firstSize hn0
      hprep.leafRefs.firstReach)
    hprep.searchOk.labSize
    (isPerm_of_cellsReach hprep.searchOk.labSize hn0
      hprep.searchOk.reach)
    hsymm hloop heq hsent (by simp) hpass
  constructor
  · constructor
    · exact hreceipt
    · rw [hout]
      exact hevent
    · exact TrailExt.refl level trail
  · refine ⟨leaf.gcaFirst, ?_, hbelow, ?_, ?_⟩
    · rw [hout, hreturn]
    · rw [hout]
      exact Or.inl (processnode_frames ctx level n leaf).2.2.2.2.2.2.1.symm
    · rw [hout]
      exact ⟨payload, hloc⟩

/-- A discrete code-two row tie closes the complete node outcome for both
the canonical-guide and first-ancestor orbit return arms. -/
theorem NodeInv.tiedLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hcc : (otherLeafSt ctx level numcells st).compCanon = 0)
    (hge : ¬(level < (otherLeafSt ctx level numcells st).canonlevel))
    (htie : (testcanlab ctx (updatecan ctx
      (otherLeafSt ctx level numcells st).canong
      (otherLeafSt ctx level numcells st).canonlab
      (otherLeafSt ctx level numcells st).samerows)
      (otherLeafSt ctx level numcells st).lab).1 = 0)
    (hcoset : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.cosetindex < n)
    (horbit : OrbSound (OrbConn (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace.toList n)
      (processnode ctx level n
        (otherLeafSt ctx level numcells st)).2.orbits n)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best trail trail
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
    ∃ target,
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 =
        Int.ofNat target ∧
      target < level ∧
      (target = (otherNode ctx inf tcLevel (fuel + 1) level numcells
          st).2.gcaFirst ∨
        target = (otherNode ctx inf tcLevel (fuel + 1) level numcells
          st).2.gcaCanon) ∧
      ∃ payload : Unwind ctx tcLevel target
          (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2 best,
        payload.Located trail := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcanonBelow : leaf.gcaCanon < level := by
    change (otherLeafSt ctx level numcells st).gcaCanon < level
    rw [RefTrail.otherLeaf_gcaCanon]
    exact hnode.canonBelow
  have hfirstBelow : leaf.gcaFirst < level :=
    Nat.lt_of_le_of_lt hlive'.order hcanonBelow
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, -, houtBest⟩ := hprep.tiedEvent hn0
    hsymm hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hcc hge
    htie hcanonBelow hlive'
  rw [houtBest] at hevent
  have hrows : leafRows ctx leaf.canonlab = leafRows ctx leaf.lab :=
    rows_eq_of_testcanlab_tie hprep.canongInv htie
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
      numcells best best
      (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 := by
    apply otherNode_leaf_tiedReceipt hnum hprep.guides hprep.trailOk
      hprep.canonPositive hcanonBelow hgsz hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach) hrows hef hcc hge htie hprep.firstPositive hfirstBelow hcoset
      horbit
  have hreturns := (processnode_rowTie (ctx := ctx) (level := level)
    (numcells := n) (st := leaf) hef (by simp) hcc hge htie).1
  have hearly : (processnode ctx level n leaf).1 <
      Int.ofNat level := by
    rcases hreturns with hfirst | hcanon
    · rw [hfirst]
      exact Int.ofNat_lt.mpr hfirstBelow
    · rw [hcanon]
      exact Int.ofNat_lt.mpr hcanonBelow
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  obtain ⟨target, hreturn, hbelow, hcontrol, payload, hloc⟩ :=
    hprep.guides.tiedUnwind (numcells := n) hprep.trailOk
      hprep.canonPositive hcanonBelow hgsz hprep.leafRefs.canonSize
      (isPerm_of_cellsReach hprep.leafRefs.canonSize hn0
        hprep.leafRefs.canonReach)
      hprep.searchOk.labSize
      (isPerm_of_cellsReach hprep.searchOk.labSize hn0
        hprep.searchOk.reach) hrows hef (by simp) hcc hge htie hprep.firstPositive
      hfirstBelow hcoset horbit
  constructor
  · constructor
    · exact hreceipt
    · rw [hout]
      exact hevent
    · exact TrailExt.refl level trail
  · refine ⟨target, ?_, hbelow, ?_, ?_⟩
    · rw [hout]
      exact hreturn
    · rw [hout]
      exact hcontrol
    · rw [hout]
      exact ⟨payload, hloc⟩

/-- An early non-generator leaf absorbs its singleton subtree and returns
the explicit local-prune outcome. -/
theorem NodeInv.plainLeaf {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hearly : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level)
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      outBest = some (incMax best
        (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  have hreturn : (processnode ctx level n leaf).1 ≤
      Int.ofNat level - 1 := Int.le_sub_one_iff.mpr hearly
  obtain ⟨bs', hevent, hmax⟩ := hprep.leafEvent hn0 hsymm
    hloop hlevel hfull hstem (by omega) hcheap' hef (by simp) hreturn hgen
    hlive'
  let outKey := incKey ctx bs'
    (processnode ctx level n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st
      (processnode ctx level n leaf).2 numcells best (some outKey)
      (processnode ctx level n leaf).1 := by
    apply NodeReceipt.pruned (NodeSound.ofExact houtFull)
      (processnode ctx level n leaf).1 rfl hearly
    · apply processnode_installed hlevel
      apply Nat.ne_of_gt
      rw [hprep.codeInv.blen]
      cases bs with
      | nil => exact (hprep.bestCodes rfl).elim
      | cons _ _ => simp
    · simpa only [outKey] using hevent.read
    · exact houtFull
  have hout := otherNode_leaf_early ctx inf tcLevel fuel level numcells st
    hnum hearly
  refine ⟨some outKey, ?_, houtFull⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hevent
  · exact TrailExt.refl level trail

/-- A non-generator leaf that does not unwind completes after the empty
child sweep and returns the exact singleton-subtree maximum. -/
theorem NodeInv.plainLeafDone {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel fuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}
    (hn0 : 0 < n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hlevel : 1 ≤ level) (hpath : level = codes.length + 1)
    (hcheap : st.noncheaplevel ≤ level)
    (hnum : (refine ctx level st.lab st.ptn st.active
      numcells).numcells = n)
    (hdisc : discreteAt (refine ctx level st.lab st.ptn st.active
      numcells).ptn level n = true)
    (hef : ¬(((otherLeafSt ctx level numcells st).eqlevFirst == level) =
      true))
    (hgen : (processnode ctx level n
      (otherLeafSt ctx level numcells st)).2.genTrace =
        (otherLeafSt ctx level numcells st).genTrace)
    (hdone : ¬((processnode ctx level n
      (otherLeafSt ctx level numcells st)).1 < Int.ofNat level))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail) :
    ∃ outBest,
      NodeOutcome G ctx tcLevel (specFuel + 1) (fuel + 1) level codes fs st
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).2
        numcells best outBest trail trail
        (otherNode ctx inf tcLevel (fuel + 1) level numcells st).1 ∧
      outBest = some (incMax best
        (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
  let leaf := otherLeafSt ctx level numcells st
  let full := codes ++
    [(refine ctx level st.lab st.ptn st.active numcells).longcode]
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  have hstem : full.take codes.length = codes := by
    simp only [full, List.take_left']
  have hprep : RunPrep G ctx tcLevel level full bs fs n leaf best
      trail := by
    simpa only [full, leaf, hnum] using
      hnode.run.otherLeaf hn0 hlevel hpath
  have hlive' : Live ctx level leaf trail := by
    simpa only [leaf] using hlive.otherLeaf (numcells := numcells)
  have hcheap' : leaf.noncheaplevel ≤ level := by
    change (otherLeafSt ctx level numcells st).noncheaplevel ≤ level
    rw [RefTrail.otherLeaf_noncheaplevel]
    exact hcheap
  obtain ⟨bs', hevent, hmax, -⟩ := hprep.leaf hn0 hsymm
    hloop hlevel hfull hcheap' hef (by simp)
  let outKey := incKey ctx bs'
    (processnode ctx level n leaf).2.canonlab
  have hleafLab : leaf.lab =
      (refine ctx level st.lab st.ptn st.active numcells).lab := by
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let base : SearchSt n :=
      { st with
        lab := rs.lab
        ptn := rs.ptn
        active := rs.active
        numnodes := st.numnodes + 1 }
    simpa only [leaf, otherLeafSt, rs, base] using
      (otherNodePrep_frames level rs.longcode base).2.2.2.2.2.2.2.2.2.2.2.1
  have hnodeKey : nodeKey ctx tcLevel (specFuel + 1) level codes st
      numcells = pathLeafKey ctx full leaf.lab := by
    unfold nodeKey
    rw [specNode_discrete hdisc, prefixKey_leafKey, hleafLab]
  have houtFull : some outKey = some (incMax best
      (nodeKey ctx tcLevel (specFuel + 1) level codes st numcells)) := by
    rw [hprep.incumbent, incMax, hnodeKey]
    exact congrArg some hmax
  let final := leafFinish level
    (processnode ctx level n leaf).2
  have hread : stInc ctx final = some outKey := by
    change stInc ctx (leafFinish level
      (processnode ctx level n leaf).2) = some outKey
    rw [stInc_leafFinish]
    simpa only [outKey] using hevent.read
  have hfinalEvent : EventOut G ctx tcLevel codes fs final
      (some outKey) trail (Int.ofNat level - 1) := by
    apply EventOut.intro level full bs' hevent.leafFinish hfull hstem
      (by omega)
    · omega
    · have hs := ReturnStab.leafFinish (level := level)
        (hlive'.stable.ofGenTraceEq hgen)
      have hfirst : final.gcaFirst = leaf.gcaFirst := by
        unfold final Nauty.leafFinish
        split <;> simp only <;> split <;>
          exact (processnode_frames ctx level n leaf).2.2.2.2.2.2.1
      rw [hfirst]
      exact hs.lower (by omega)
    · exact (hlive'.history.processnode hprep.trailOk).leafFinish
  have hreceipt : NodeReceipt trail ctx tcLevel (specFuel + 1)
      (fuel + 1) level codes st final numcells best (some outKey)
      (Int.ofNat level - 1) := by
    apply NodeReceipt.complete (NodeSound.ofExact houtFull) rfl
    · exact canonlevel_ne_zero_of_stInc hread
    · exact hread
    · exact houtFull
  have hout := otherNode_leaf_done_state ctx inf tcLevel fuel level
    numcells st hnum hdone
  refine ⟨some outKey, ?_, houtFull⟩
  constructor
  · rw [hout]
    exact hreceipt
  · rw [hout]
    exact hfinalEvent
  · exact TrailExt.refl level trail

/-! # Completed child sweeps -/

/-- An empty positive-fuel first-path sweep closes the coupled loop
outcome.  The comparison sign is explicit: a freshly prepared node may
enter its first child with sign one, whereas every state that reaches the
end of a real sweep has already absorbed a child and restored a
nonpositive sign. -/
theorem LoopInv.firstDone {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 index : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).2.2
      best best trail trail
      (firstChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell index st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact firstLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell index
      cursor _ st best trail hinstalled hread hinv.cover hnext
  · simpa only [firstChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

/-- An empty positive-fuel off-path sweep closes the coupled loop outcome
with the same frozen-frame coverage and result event. -/
theorem LoopInv.otherDone {G : Colored n k} {ctx : Ctx n}
    {inf tcLevel specFuel runFuel loopFuel level numcells tc len tv1 : Nat} {tcell : VSet n}
    {stem codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {bound : Key n} {base st : SearchSt n}
    {best : Option (Key n)}
    {trail : FrameTrail}
    (hpath : level = codes.length)
    (hstem : codes.take stem.length = stem)
    (hpast : stem.length < level)
    (hnext : tcell.nextElem cursor = none)
    (hnp : st.compCanon ≤ 0)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hlive : Live ctx level st trail) :
    LoopOutcome G ctx tcLevel specFuel runFuel (loopFuel + 1) level stem
      codes fs rsLab rsPtn tc len numcells tcell cursor
      bound
      st
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).2
      best best trail trail
      (otherChildLoop ctx inf tcLevel runFuel (loopFuel + 1) level
        numcells tc tv1 none tcell st).1 := by
  have hread : stInc ctx st = best := hinv.run.read (by omega)
  have hreadSome : stInc ctx st =
      some (incKey ctx bs st.canonlab) :=
    hread.trans hinv.run.incumbent
  have hinstalled : st.canonlevel ≠ 0 :=
    canonlevel_ne_zero_of_stInc hreadSome
  constructor
  · exact otherLoop_doneReceipt ctx inf tcLevel specFuel runFuel
      loopFuel level numcells tc tv1 codes rsLab rsPtn len tcell cursor _
      st best trail hinstalled hread hinv.cover hnext
  · simpa only [otherChildLoop, loopReturn] using
      (EventOut.ofRun hinv.run hpath hstem hpast (by omega) hnp
        (hlive.stable.lower (by omega)) hlive.history)
  · exact TrailExt.refl level trail

end Hex.GraphIso.Nauty

/-!
`cosetindex` is a first-path loop cursor.  The first-path loop overwrites
it when it chooses a new sibling, but the whole `otherNode` subtree below
that sibling leaves it unchanged.  These equations isolate that executable
fact; orbit-return coverage may use the cursor only on the off-path side.
-/

namespace Hex.GraphIso.Nauty

private theorem pushAuto_coset (st : SearchSt n) (pair : VSet n × VSet n) :
    (pushAuto st pair).cosetindex = st.cosetindex := by
  rw [pushAuto]
  split <;> rfl

/-- Leaf classification never changes the first-path coset cursor. -/
theorem processnode_coset (ctx : Ctx n) (level numcells : Nat)
    (st : SearchSt n) :
    (processnode ctx level numcells st).2.cosetindex = st.cosetindex := by
  rw [processnode]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun x : Int × SearchSt n => x.2.cosetindex),
    pushAuto_coset, ite_self]

/-- Comparison preparation never changes the first-path coset cursor. -/
theorem otherNodePrep_coset (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).cosetindex = st.cosetindex := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.cosetindex, ite_self]

/-- Parent-frame recovery never changes the first-path coset cursor. -/
theorem recover_coset (n inf level : Nat) (st : SearchSt n) :
    (recover n inf level st).cosetindex = st.cosetindex := by
  rw [recover]
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.cosetindex, ite_self]

/-- Completed-leaf cleanup never changes the first-path coset cursor. -/
theorem leafFinish_coset (level : Nat) (st : SearchSt n) :
    (leafFinish level st).cosetindex = st.cosetindex := by
  rw [leafFinish]
  split <;> split <;> rfl

end Hex.GraphIso.Nauty
