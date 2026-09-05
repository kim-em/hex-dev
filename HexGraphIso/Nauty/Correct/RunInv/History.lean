/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Frames
public import HexGraphIso.Nauty.Correct.Unwind.Target

public section

/-!
The reference-leaf history and the result-side state of a recursive
node.

`RefTrail` records that a referenced leaf descends from every intervening
active frame, which the mutable `gcaFirst` and `gcaCanon` controls do not
say by themselves.  `EventOut` existentially carries the full comparison
path a returned state reached, exposing only the prefix its caller
needs.
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
