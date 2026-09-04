/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SearchOutcomeResult

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
structure RefTrail (ctx : Ctx) (current : Nat) (st : SearchSt)
    (trail : FrameTrail) : Prop where
  frameSize : ∀ target entry, target < current →
    trail target = some entry → entry.frame.rsLab.size = ctx.n
  first : ∀ target entry, target < current →
    target ≤ st.gcaFirst → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.firstlab
  canon : ∀ target entry, target < current →
    target ≤ st.gcaCanon → trail target = some entry →
    cellsPerm entry.frame.rsPtn target entry.frame.rsLab st.canonlab

namespace RefTrail

/-- The empty trail has no reference-history obligations. -/
theorem empty (ctx : Ctx) (current : Nat) (st : SearchSt) :
    RefTrail ctx current st FrameTrail.empty := by
  constructor
  · intro target entry _ hentry
    simp [FrameTrail.empty] at hentry
  · intro target entry _ _ hentry
    simp [FrameTrail.empty] at hentry
  · intro target entry _ _ hentry
    simp [FrameTrail.empty] at hentry

/-- Reference history depends only on the two references and their GCA
controls. -/
theorem stateEq {ctx : Ctx} {current : Nat} {st st' : SearchSt}
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

/-- Recovering an ancestor preserves both reference histories.  The
canonical control may be clamped to the recovered level, which only
weakens its reach obligation. -/
theorem recover {ctx : Ctx} {current level inf : Nat} {st : SearchSt}
    {trail : FrameTrail} (h : RefTrail ctx current st trail)
    (hle : level ≤ current) :
    RefTrail ctx level (Nauty.recover ctx.n inf level st) trail := by
  obtain ⟨hcanon, -, -, -, hfirst, -, hgcaFirst, -, -, -⟩ :=
    recover_frames ctx.n inf level st
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
theorem processnode {ctx : Ctx} {level numcells : Nat} {st : SearchSt}
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

/-- Pushing a child frame extends reference history.  At the new frame,
the loop's two reference receipts discharge the cases whose GCA control
is exactly the parent level. -/
theorem push {ctx : Ctx} {level : Nat} {st : SearchSt}
    {trail : FrameTrail} {entry : TrailEntry}
    (h : RefTrail ctx level st trail)
    (hfirstBound : st.gcaFirst ≤ level)
    (hcanonBound : st.gcaCanon ≤ level)
    (hsize : entry.frame.rsLab.size = ctx.n)
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

/-- A scatter from the first reference onto the current labelling
stabilizes every active frame to which `gcaFirst` permits a return. -/
theorem firstStab {ctx : Ctx} {current : Nat} {st : SearchSt}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hfirstSize : st.firstlab.size = ctx.n)
    (hbelow : st.gcaFirst < current)
    (hmap : ∀ i, i < ctx.n →
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

/-- A scatter from the canonical reference onto the current labelling
stabilizes every active frame through any bound no deeper than
`gcaCanon`.  The smaller bound is needed by code two's orbit return to
`gcaFirst`. -/
theorem canonStabTo {ctx : Ctx} {current limit : Nat} {st : SearchSt}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hcanonSize : st.canonlab.size = ctx.n)
    (hle : limit ≤ st.gcaCanon) (hbelow : limit < current)
    (hmap : ∀ i, i < ctx.n →
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

/-- The exact canonical-GCA instance of `canonStabTo`. -/
theorem canonStab {ctx : Ctx} {current : Nat} {st : SearchSt}
    {trail : FrameTrail} {gamma : Array Nat}
    (h : RefTrail ctx current st trail)
    (htrail : TrailOk ctx current st trail)
    (hcanonSize : st.canonlab.size = ctx.n)
    (hbelow : st.gcaCanon < current)
    (hmap : ∀ i, i < ctx.n →
      gamma[st.canonlab[i]!]! = st.lab[i]!) :
    ∀ target entry, Int.ofNat target ≤ Int.ofNat st.gcaCanon →
      trail target = some entry →
      CellStab entry.frame.rsPtn target entry.frame.rsLab gamma := by
  exact h.canonStabTo htrail hcanonSize (Nat.le_refl _) hbelow hmap

end RefTrail

end Hex.GraphIso.Nauty
