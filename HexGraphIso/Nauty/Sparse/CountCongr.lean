/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountClasses

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Equal input count multisets yield identical ordered output counts in
the actual splitter. Other scratch fields need not agree. -/
theorem splitCounts_keys (level first last : Nat) (distance : Bool) (s t : RefineSt n)
    (hsl : s.lab.size = n) (htl : t.lab.size = n)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : s.hits[s.lab[first]!]! < n + 2) (htk : t.hits[t.lab[first]!]! < n + 2)
    (hp : ((segN s.lab first (last + 1 - first)).map fun v => s.hits[v]!).Perm
      ((segN t.lab first (last + 1 - first)).map fun v => t.hits[v]!))
    (hq : first ≤ q) (he : q ≤ last) :
    s.hits[(splitCounts level first distance s).lab[q]!]! =
      t.hits[(splitCounts level first distance t).lab[q]!]! := by
  have hs := splitCounts_sorted level first distance s (by omega) (by omega) hsk
  have ht := splitCounts_sorted level first distance t (by omega) (by omega) htk
  have hsp := splitCounts_segment level first distance s (by omega) (by omega)
  have htp := splitCounts_segment level first distance t (by omega) (by omega)
  have hsiz := perm_size (splitCounts_perm level first distance s (by omega) (by omega))
  have htiz := perm_size (splitCounts_perm level first distance t (by omega) (by omega))
  rw [hse] at hs hsp
  rw [hte] at ht htp
  have hsseg : (segN (splitCounts level first distance s).lab first (last + 1 - first)).Perm
      (segN s.lab first (last + 1 - first)) := by
    rw [segN_extract _ _ _ (by omega), segN_extract _ _ _ (by omega),
      show first + (last + 1 - first) = last + 1 by omega]
    exact hsp
  have htseg : (segN (splitCounts level first distance t).lab first (last + 1 - first)).Perm
      (segN t.lab first (last + 1 - first)) := by
    rw [segN_extract _ _ _ (by omega), segN_extract _ _ _ (by omega),
      show first + (last + 1 - first) = last + 1 by omega]
    exact htp
  exact hs.keys_eq ht ((hsseg.map _).trans (hp.trans (htseg.map _).symm)) hq (by omega)

/-- Count splitting writes the same partition for equal cell key multisets.
This is literal array equality, including inherited boundary values. -/
theorem splitCounts_ptn (level first last : Nat) (distance : Bool) (s t : RefineSt n)
    (hsl : s.lab.size = n) (htl : t.lab.size = n)
    (hsp : s.ptn.size = n) (htp : t.ptn = s.ptn)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2)
    (htk : ∀ q, first ≤ q → q ≤ last → t.hits[t.lab[q]!]! < n + 2)
    (hp : ((segN s.lab first (last + 1 - first)).map fun v => s.hits[v]!).Perm
      ((segN t.lab first (last + 1 - first)).map fun v => t.hits[v]!)) :
    (splitCounts level first distance s).ptn = (splitCounts level first distance t).ptn := by
  have hs := splitCounts_partition level first distance s hsl hsp (by omega) (by omega)
    (fun q hq he => hsk q hq (by omega))
  have ht := splitCounts_partition level first distance t htl (by rw [htp]; exact hsp)
    (by omega) (by omega) (fun q hq he => htk q hq (by omega))
  rw [hse] at hs
  rw [hte, htp] at ht
  exact hs.eq_ptn ht (fun q hq he => splitCounts_keys level first last distance s t
    hsl htl hse hte hf hb (hsk first (by omega) hf) (htk first (by omega) hf) hp hq he)

end Hex.GraphIso.Nauty.Sparse
