/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceTarget

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Supplying the unhinted target as a hint leaves the target unchanged,
whether the hint guard accepts it or dispatches to the unhinted rule. -/
theorem targetcell_hint (g : Graph n) (lab ptn : Array Nat) (level tcLevel : Nat) :
    targetcell g lab ptn level tcLevel (Int.ofNat (targetcell g lab ptn level tcLevel (-1))) =
      targetcell g lab ptn level tcLevel (-1) := by
  simp [targetcell]

/-- Cached hint dispatch retains the complete target position, vertex set
and size when the hint agrees with the unhinted rule. Scratch may change. -/
theorem targetCached_hint (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level tcLevel : Nat)
    (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (hi : Scratch.Valid n lab ptn level s)
    (hc : bcount ptn level n < n) {hint : Int}
    (hh : Int.ofNat (targetcell (.ofGraph G) lab ptn level tcLevel (-1)) = hint) :
    let a := maketargetCached (.ofGraph G) lab ptn level tcLevel hint s
    let b := maketargetCached (.ofGraph G) lab ptn level tcLevel (-1) s
    (a.1, a.2.1, a.2.2.1) = (b.1, b.2.1, b.2.2.1) := by
  have ha := maketargetCached_eq G lab ptn level tcLevel hint s l hl hs hend hi (Target.nonempty hs hend hc)
  have hb := maketargetCached_eq G lab ptn level tcLevel (-1) s l hl hs hend hi (Target.nonempty hs hend hc)
  apply ha.trans
  rw [hb]
  rw [← hh]
  simp only [maketargetcell, targetcell_hint]

/-- The actual cached target fields agree with unhinted selection along a
live history below a cheap ancestor, using the stored first target as hint. -/
theorem FirstRef.cached_target {G : Hex.SparseGraph n} {tcLevel base level : Nat}
    {root current : RefineSt n} {st : State n}
    (h : FirstRef G tcLevel base root st) (hdepth : level ≤ h.last)
    (hr : RefineSt.Ready G base root) (hc : RefineSt.Ready G level current)
    (hshape : NodeShape n base root.ptn)
    (hp : FollowsPerm G st.firsttc base root level current)
    (hopen : discreteAt current.ptn level n ≠ true)
    (scratch : Scratch) (hs : Scratch.Valid n current.lab current.ptn level scratch) :
    let a := maketargetCached (.ofGraph G) current.lab current.ptn level tcLevel st.firsttc[level]! scratch
    let b := maketargetCached (.ofGraph G) current.lab current.ptn level tcLevel (-1) scratch
    (a.1, a.2.1, a.2.2.1) = (b.1, b.2.1, b.2.2.1) := by
  have hh := h.target hdepth hr hc hshape hp hopen
  have hbound : bcount current.ptn level n < n := by
    have hb := bcount_le current.ptn level n
    have hn : bcount current.ptn level n ≠ n := fun he =>
      hopen ((discreteAt_iff_bcount hc.spec.node.ptnSize.symm hc.spec.node.ptnEnd).mpr he)
    omega
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hc.spec.label
  exact targetCached_hint G current.lab current.ptn level tcLevel scratch l hl hc.spec.node.ptnSize
    (by simpa only [hc.spec.node.ptnSize] using hc.spec.node.ptnEnd) hs hbound hh

end Hex.GraphIso.Nauty.Sparse
