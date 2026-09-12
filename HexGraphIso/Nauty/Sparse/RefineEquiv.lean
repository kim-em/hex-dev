/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SingletonEquiv
public import HexGraphIso.Nauty.Sparse.NontrivialEquiv
public import HexGraphIso.Nauty.Sparse.RefineState

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt

/-- Observable refinement equivalence allows independent scratch layouts,
generations and orders within corresponding cells. -/
structure Equiv (σ : Renaming n) (level : Nat) (s t : RefineSt n) : Prop where
  ptn : t.ptn = s.ptn
  cells : cellsPerm s.ptn level t.lab (s.lab.map σ.toFun)
  control : CountTrace.control s = CountTrace.control t
  count : s.numcells = t.numcells

namespace Equiv

variable {σ : Renaming n} {level : Nat} {s t : RefineSt n}

theorem active (h : Equiv σ level s t) : s.active = t.active :=
  congrArg CountTrace.Control.active h.control

theorem queue (h : Equiv σ level s t) : s.queue = t.queue :=
  congrArg CountTrace.Control.queue h.control

theorem code (h : Equiv σ level s t) : s.longcode = t.longcode :=
  congrArg CountTrace.Control.code h.control

/-- The literal hash transition respects the observation relation. -/
theorem hash (h : Equiv σ level s t) (v : Nat) : Equiv σ level (s.hash v) (t.hash v) :=
  ⟨h.ptn, h.cells, congrArg (fun c => c.hash v) h.control, h.count⟩

/-- The production swap/pop removal respects the ordered-queue relation. -/
theorem remove (h : Equiv σ level s t) (pos : Nat) :
    Equiv σ level
      { s with
        active := s.active.erase s.queue[pos]!
        queue := (s.queue.set! pos s.queue[s.queue.size - 1]!).pop }
      { t with
        active := t.active.erase t.queue[pos]!
        queue := (t.queue.set! pos t.queue[t.queue.size - 1]!).pop } := by
  refine ⟨h.ptn, h.cells, ?_, h.count⟩
  simp only [CountTrace.control, h.active, h.queue, h.code]

/-- Every actual count split transports under local key agreement. -/
theorem counts (h : Equiv σ level s t) (first : Nat) (distance : Bool)
    (hs : Valid level s) (ht : Valid level t)
    (hc : IsCell s.ptn level first (s.cellend[first]! + 1 - first))
    (hb : s.cellend[first]! < n)
    (hk : ∀ q, first ≤ q → q ≤ s.cellend[first]! → s.hits[s.lab[q]!]! < n + 2)
    (hk' : ∀ q, first ≤ q → q ≤ t.cellend[first]! → t.hits[t.lab[q]!]! < n + 2)
    (hv : ∀ v ∈ segN s.lab first (s.cellend[first]! + 1 - first), t.hits[σ v]! = s.hits[v]!) :
    Equiv σ level (splitCounts level first distance s) (splitCounts level first distance t) := by
  have hf : first ≤ s.cellend[first]! := by have := hc.1; omega
  have hi := ht.index
  rw [h.ptn] at hi
  have he := hs.index.ends_congr hi hc (by omega)
  have hh := splitCounts_equiv σ level first s.cellend[first]! distance s t hs.lab ht.lab hs.size h.ptn
    rfl he.symm hf hb hk (fun q hq hb => hk' q hq (by omega)) hv hc h.cells h.control h.count
  exact ⟨hh.1.symm, hh.2.1, hh.2.2.1, hh.2.2.2⟩

end Equiv
end Hex.GraphIso.Nauty.Sparse.RefineSt
