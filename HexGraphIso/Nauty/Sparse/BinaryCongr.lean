/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryEquiv
import all HexGraphIso.Nauty.Sparse.BinaryCell
import all HexGraphIso.Nauty.Spec.CellPerm

public section

namespace Hex.GraphIso.Nauty.Sparse.Binary

/-- The compaction cut depends only on the input labels and observed
predicate, rather than on the retained mark values or generation number. -/
theorem cut_congr {lab other : Array Nat} {pred test : Nat → Bool}
    (hl : other = lab) (hk : ∀ v ∈ seen lab first last, test v = pred v) :
    cut other test first last = cut lab pred first last := by
  unfold cut
  rw [hl]
  have he := List.filter_congr (fun v hv => congrArg Bool.not (hk v hv))
  exact congrArg (fun xs : List Nat => first + xs.length) he

/-- Equal inputs and observed marks close precisely the same boundary. -/
theorem Cell.ptn_eq {s t a b : RefineSt n}
    (hs : Cell level first last pred s a) (ht : Cell level first last other t b)
    (hl : t.lab = s.lab) (hp : t.ptn = s.ptn)
    (hk : ∀ v ∈ seen s.lab first last, other v = pred v) : a.ptn = b.ptn := by
  rw [hs.ptn, ht.ptn, cut_congr hl hk, hp]

/-- Identical singleton-cell input orders and mark predicates give
identical output arrays. Retained marks outside this cell and the numeric
generation need not agree. -/
theorem Cell.lab_eq {s t a b : RefineSt n}
    (hs : Cell level first last pred s a) (ht : Cell level first last other t b)
    (hl : t.lab = s.lab) (hf : first ≤ last)
    (hk : ∀ v ∈ seen s.lab first last, other v = pred v) : a.lab = b.lab := by
  have hkept : ((seen s.lab first last).filter fun v => !pred v) =
      ((seen s.lab first last).filter fun v => !other v) :=
    List.filter_congr (fun v hv => congrArg Bool.not (hk v hv).symm)
  have hhits : (seen s.lab first last).filter pred = (seen s.lab first last).filter other :=
    List.filter_congr (fun v hv => (hk v hv).symm)
  have hcut := cut_congr hl hk
  have hleft : segN a.lab first (cut s.lab pred first last - first) =
      segN b.lab first (cut s.lab pred first last - first) := by
    rw [hs.retained, ← hcut, ht.retained, hl, hkept]
  have hright : segN a.lab (cut s.lab pred first last) (last - cut s.lab pred first last) =
      segN b.lab (cut s.lab pred first last) (last - cut s.lab pred first last) := by
    rw [hs.collected, ← hcut, ht.collected, hl, hhits]
  have bounds := cut_bounds s.lab pred hf
  apply Array.ext
  · rw [hs.frame.lab_size, ht.frame.lab_size, hl]
  · intro q hqa hqb
    by_cases hout : q < first ∨ last ≤ q
    · have he := (hs.window.outside q hout).trans ((congrArg (fun lab : Array Nat => lab[q]!) hl).symm.trans
        (ht.window.outside q hout).symm)
      simpa only [getElem!_pos a.lab q hqa, getElem!_pos b.lab q hqb] using he
    · by_cases hq : q < cut s.lab pred first last
      · have he := congrArg (fun xs : List Nat => xs[q - first]!) hleft
        simpa [segN,
          show q - first < cut s.lab pred first last - first by omega,
          show first + (q - first) = q by omega, hqa, hqb] using he
      · have he := congrArg (fun xs : List Nat => xs[q - cut s.lab pred first last]!) hright
        simpa [segN,
          show q - cut s.lab pred first last < last - cut s.lab pred first last by omega,
          show cut s.lab pred first last + (q - cut s.lab pred first last) = q by omega, hqa, hqb] using he

end Hex.GraphIso.Nauty.Sparse.Binary
