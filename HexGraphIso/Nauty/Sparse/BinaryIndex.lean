/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BinaryControl
public import HexGraphIso.Nauty.Sparse.CompactIndex

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual binary finalization writes exactly the cache justified by
compaction and reverse fill, including both uniform predicate classes. -/
theorem Binary.Result.cache {s r : RefineSt n} (h : Binary.Result level first cut last s lab starts r)
    (hc : Compact before p first last seen temp hit cut)
    (hseen : seen = (before.toList.drop first).take (last - first))
    (hf : Fill temp hit.toList.reverse cut hit.toList.reverse.length lab)
    (hw : Index.Writes n oldstarts starts hit.toList.reverse cut)
    (hp : before.toList.Perm (List.range n)) (hptn : s.ptn.size = n)
    (hi : Index.Valid n before s.ptn level oldstarts s.cellend)
    (hcell : IsCell s.ptn level first (last - first)) (hn : first + 1 < last) :
    Index.Valid n r.lab r.ptn level r.cellstart r.cellend := by
  rw [h.label, h.ptn, h.starts_eq, h.ends]
  simpa only [Array.set!_eq_setIfInBounds] using hc.cache hseen hf hw hp hptn hi hcell hn

end Hex.GraphIso.Nauty.Sparse
