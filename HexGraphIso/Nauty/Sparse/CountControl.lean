/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountExecution
public import HexGraphIso.Nauty.Sparse.CountCompare
public import HexGraphIso.Nauty.Sparse.CountSize

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Equal cell count multisets and initial control yield literally equal
hashes, active sets and ordered queues in the executed splitter. Scratch
storage and vertex order may differ. -/
theorem splitCounts_control (level first last : Nat) (distance : Bool) (s t : RefineSt n)
    (hsl : s.lab.size = n) (htl : t.lab.size = n)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2)
    (htk : ∀ q, first ≤ q → q ≤ last → t.hits[t.lab[q]!]! < n + 2)
    (hc : CountTrace.control s = CountTrace.control t)
    (hp : ((segN s.lab first (last + 1 - first)).map fun v => s.hits[v]!).Perm
      ((segN t.lab first (last + 1 - first)).map fun v => t.hits[v]!)) :
    CountTrace.control (splitCounts level first distance s) =
      CountTrace.control (splitCounts level first distance t) := by
  have hs := splitCounts_trace level first distance s hsl (by omega) (by omega)
    (fun q hq he => hsk q hq (by omega))
  have ht := splitCounts_trace level first distance t htl (by omega) (by omega)
    (fun q hq he => htk q hq (by omega))
  rw [hse] at hs
  rw [hte] at ht
  exact hs.control_eq ht hc (CountTrace.uniform_iff s.lab t.lab s.hits t.hits (by omega) hp)
    (fun q hq he => splitCounts_keys level first last distance s t hsl htl hse hte hf hb
      (hsk first (Nat.le_refl _) hf) (htk first (Nat.le_refl _) hf) hp hq (by omega))

/-- All count-split observations commute with renaming and within-cell
permutation: ordered partition, cell contents, control and exact count.
Only the divided cell's hit values must agree under the renaming. -/
theorem splitCounts_equiv (σ : Renaming n) (level first last : Nat) (distance : Bool)
    (s t : RefineSt n)
    (hsl : s.lab.toList.Perm (List.range n)) (htl : t.lab.toList.Perm (List.range n))
    (hsp : s.ptn.size = n) (htp : t.ptn = s.ptn)
    (hse : s.cellend[first]! = last) (hte : t.cellend[first]! = last)
    (hf : first ≤ last) (hb : last < n)
    (hsk : ∀ q, first ≤ q → q ≤ last → s.hits[s.lab[q]!]! < n + 2)
    (htk : ∀ q, first ≤ q → q ≤ last → t.hits[t.lab[q]!]! < n + 2)
    (hk : ∀ v ∈ segN s.lab first (last + 1 - first), t.hits[σ v]! = s.hits[v]!)
    (hc : IsCell s.ptn level first (last + 1 - first))
    (hp : cellsPerm s.ptn level t.lab (s.lab.map σ.toFun))
    (hcontrol : CountTrace.control s = CountTrace.control t) (hnum : s.numcells = t.numcells) :
    (splitCounts level first distance s).ptn = (splitCounts level first distance t).ptn ∧
      cellsPerm (splitCounts level first distance s).ptn level
        (splitCounts level first distance t).lab ((splitCounts level first distance s).lab.map σ.toFun) ∧
      CountTrace.control (splitCounts level first distance s) =
        CountTrace.control (splitCounts level first distance t) ∧
      (splitCounts level first distance s).numcells = (splitCounts level first distance t).numcells := by
  have hs : s.lab.size = n := by simpa using hsl.length_eq
  have ht : t.lab.size = n := by simpa using htl.length_eq
  obtain ⟨hptn, hcells⟩ := splitCounts_map σ level first last distance s t hsl htl hsp htp
    hse hte hf hb hsk htk hk hc hp
  have hkeys := (segment_keys_map σ s.lab t.lab s.hits t.hits hsl (by omega) (hp _ _ hc) hk).symm
  refine ⟨hptn, hcells, splitCounts_control level first last distance s t hs ht hse hte hf hb
    hsk htk hcontrol hkeys, ?_⟩
  have hsc := splitCounts_count level first distance s hs hsp (by omega)
    (by simpa only [hse] using hc) (fun q hq he => hsk q hq (by omega))
  have htc := splitCounts_count level first distance t ht (by rw [htp]; exact hsp) (by omega)
    (by simpa only [hte, htp] using hc) (fun q hq he => htk q hq (by omega))
  rw [htp] at htc
  rw [hptn, hnum] at hsc
  omega

end Hex.GraphIso.Nauty.Sparse
