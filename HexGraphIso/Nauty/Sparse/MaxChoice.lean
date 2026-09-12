/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxTarget
public import HexGraphIso.Nauty.Sparse.FirstPrepare
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Policy.Storage
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The native first path and nonnegative canonical comparisons use the
literal unhinted cached target. -/
theorem chooseTarget_unhinted {g : Graph n} {tcLevel level numcells : Nat}
    {st : State n} (first : Bool) (hc : numcells < n)
    (hh : first = true ∨ 0 ≤ st.compCanon) :
    (chooseTarget first g tcLevel level numcells st).1.toNat =
      (maketargetCached g st.lab st.ptn level tcLevel (-1) st.canong.scratch).1 := by
  cases first with
  | false =>
    have hp : 0 ≤ st.compCanon := by simpa using hh
    have hn : ¬st.compCanon < 0 := by omega
    simp [chooseTarget, hc, hp, hn]
  | true =>
    simp [chooseTarget, show numcells ≠ n by omega]

namespace Max

/-- An actual target is the original unhinted target or its entire code
prefix is dominated. The latter also bounds descendants of a hinted target. -/
def Frame.Choice (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n)
    (tc : Nat) (best : Option (Key n)) : Prop :=
  tc = (f.target G tcLevel).tc ∨
    ∀ tail : Key n, Covers (prefixKey (f.codes ++ [f.code G]) tail) best

theorem Frame.Choice.grow {G : Hex.SparseGraph n} {tcLevel tc : Nat} {f : Frame n}
    {before after : Option (Key n)} (h : f.Choice G tcLevel tc before)
    (hg : Grows before after) : f.Choice G tcLevel tc after := by
  rcases h with ht | hd
  · exact Or.inl ht
  · exact Or.inr (fun tail => (hd tail).grow hg)

/-- First-path preparation records the unhinted target before the actual
cheap check and child selection. -/
theorem Frame.first_target {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (hc : (visit (.ofGraph G) f.level f.numcells f.entry).1 < n) :
    (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.1.toNat =
      (f.target G tcLevel).tc := by
  let v := visit (.ofGraph G) f.level f.numcells f.entry
  change (chooseTarget true (.ofGraph G) tcLevel f.level v.1
    (recordFirst f.level v.2.1 v.2.2)).1.toNat = _
  rw [chooseTarget_unhinted true hc (Or.inl rfl)]
  rfl

/-- The actual off-path preparation establishes the choice alternative
from its executed code comparison. No assumption about a hinted subtree's
maximum is needed. -/
theorem Frame.Valid.choice {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} (h : f.Valid G)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n) :
    let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    f.Choice G.graph tcLevel p.2.2.1.toNat (State.key G.graph bs p.2.2.2.2.2) := by
  intro p
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  let compared := compareCodes f.level v.2.1 v.2.2
  by_cases hn : compared.compCanon < 0
  · right
    have hl := h.length
    have hd := h.depth
    have hm := hc.prepare tcLevel f.numcells (by omega)
    rw [hl] at hm
    have he : p.2.2.2.2.2.compCanon = compared.compCanon :=
      (chooseTarget_codes false (.ofGraph G.graph) tcLevel f.level v.1 compared).2.2.2.1
    exact fun tail => hm.1.covers (he ▸ hn) tail
  · left
    change (chooseTarget false (.ofGraph G.graph) tcLevel f.level v.1 compared).1.toNat = _
    rw [chooseTarget_unhinted false hi (Or.inr (by omega : 0 ≤ compared.compCanon))]
    dsimp only [compared]
    rw [(compareCodes_frame f.level v.2.1 v.2.2).1,
      (compareCodes_frame f.level v.2.1 v.2.2).2.1,
      SearchState.compare_storage]
    rfl

end Max
end Hex.GraphIso.Nauty.Sparse
