/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountCache

public section

namespace Hex.GraphIso.Nauty.Sparse.Minima.Permuted

/-- The first-fragment singleton write initializes the two-fragment index
invariant without disturbing any cell outside the split. -/
theorem indices {n : Nat} {s : RefineSt n}
    (hm : Permuted s.lab lab s.hits first last v2 v3 last w1 w2 cap)
    (hp : s.lab.toList.Perm (List.range n)) (hb : last ≤ n) (hs : s.cellstart.size = n)
    (hc : ∀ q, first ≤ q → q < last → s.cellstart[s.lab[q]!]! = first) :
    let starts := if v2 = first + 1 then s.cellstart.setIfInBounds lab[first]! n else s.cellstart
    Index.Two n first v2 v3 v2 lab starts ∧
    Index.Frame n first (last - 1) s.lab lab s.cellstart starts s.cellend s.cellend := by
  have bounds := hm.bounds
  have perm := hm.window.perm.trans hp
  have hlast : last - 1 + 1 = last := by omega
  have hfirst (q : Nat) (hq : first ≤ q) (hv : q < v2) : s.cellstart[lab[q]!]! = first := by
    obtain ⟨r, hrf, hrl, hr⟩ := hm.window.mem hm.size ⟨hq, by omega⟩
    rw [hr]
    exact hc r hrf hrl
  have ht := Index.Two.initial (v3 := v3) hs (by omega : v2 ≤ n)
    (fun _ hi => perm_bound perm hi) hfirst
  refine ⟨ht, ?_⟩
  have hf : Index.Frame n first (last - 1) s.lab lab s.cellstart s.cellstart s.cellend s.cellend := by
    apply Index.Frame.of_window
    simpa only [hlast] using hm.window
  split
  · exact hf.set_start (fun _ _ hi hj he => perm_injective perm hi hj he)
      ⟨Nat.le_refl _, by omega⟩ (by omega)
  · exact hf

/-- The singleton second fragment uses one sentinel write instead of the
scatter loop, preserving the same completed-run contract. -/
theorem indices_single {n : Nat} {s : RefineSt n}
    (hm : Permuted s.lab lab s.hits first last v2 v3 last w1 w2 cap)
    (hp : s.lab.toList.Perm (List.range n)) (hb : last ≤ n) (hs : s.cellstart.size = n)
    (hc : ∀ q, first ≤ q → q < last → s.cellstart[s.lab[q]!]! = first)
    (hv : v3 = v2 + 1) :
    let starts := (if v2 = first + 1 then s.cellstart.setIfInBounds lab[first]! n else s.cellstart)
      |>.setIfInBounds lab[v2]! n
    Index.Two n first v2 v3 v3 lab starts ∧
    Index.Frame n first (last - 1) s.lab lab s.cellstart starts s.cellend s.cellend := by
  have bounds := hm.bounds
  have perm := hm.window.perm.trans hp
  obtain ⟨ht, hf⟩ := hm.indices hp hb hs hc
  have hh := ht.step (fun i hi => perm_bound perm hi)
    (fun i j hi hj he => perm_injective perm hi hj he) (Nat.le_refl _) (by omega)
  have hframe := hf.set_start (value := n)
    (fun i j hi hj he => perm_injective perm hi hj he) (a := v2) ⟨by omega, by omega⟩ (by omega)
  refine ⟨?_, hframe⟩
  simpa only [hv, ite_true] using hh

end Hex.GraphIso.Nauty.Sparse.Minima.Permuted

namespace Hex.GraphIso.Nauty.Sparse.Index.Two

/-- A second-fragment scatter write preserves both earlier fragment entries
and all entries outside the original cell. -/
theorem set_long (ht : Two n first v2 v3 upto lab starts)
    (hf : Frame n first last oldlab lab oldstarts starts oldends ends)
    (hp : lab.toList.Perm (List.range n))
    (hfirst : first ≤ upto) (hu : v2 ≤ upto) (hlast : upto ≤ last) (hb : upto < n)
    (hv : v3 ≠ v2 + 1) :
    Two n first v2 v3 (upto + 1) lab (starts.setIfInBounds lab[upto]! v2) ∧
    Frame n first last oldlab lab oldstarts (starts.setIfInBounds lab[upto]! v2) oldends ends :=
  ⟨ht.step_long (fun _ hi => perm_bound hp hi) (fun _ _ hi hj he => perm_injective hp hi hj he)
    hu hb hv,
    hf.set_start (fun _ _ hi hj he => perm_injective hp hi hj he) ⟨hfirst, hlast⟩ hb⟩

end Hex.GraphIso.Nauty.Sparse.Index.Two
