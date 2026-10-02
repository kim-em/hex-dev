/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxEmit
public import HexGraphIso.Nauty.Sparse.FirstPrepare
public import HexGraphIso.Nauty.Sparse.CodeFields
public import HexGraphIso.Nauty.Policy.First.Compare
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.CodeRead
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.First.Compare
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

theorem Frame.code_lt (G : Hex.SparseGraph n) (f : Frame n) : f.code G < codeSentinel :=
  refineWith_code_lt (.ofGraph G) f.level f.entry.lab f.entry.ptn f.entry.active f.numcells f.entry.canong.scratch

/-- Actual first preparation extends the stored ancestor codes by its
executed refinement code at the allocated next slot. -/
theorem Frame.Valid.first_codes {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {f : Frame n}
    (h : f.Valid G) (hs : StoredCodes f.entry.firstcode 1 f.codes)
    (ha : n < f.entry.firstcode.size) :
    StoredCodes (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2.firstcode
      1 (f.codes ++ [f.code G.graph]) := by
  rw [(prepareFirst_store (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1]
  have he : 1 + f.codes.length = f.level := by have := h.length; omega
  have hp := hs.push (by have := h.depth; omega) (f.code G.graph)
  simpa only [he, Frame.code] using hp

/-- The label at an actual first discrete visit has exactly the complete
frozen node key, with the native ancestor codes and sentinel. -/
theorem Frame.Valid.first_key {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {label : Label n} (h : f.Valid G) :
    let p := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 = n → Label.ofArray? n p.2.2.2.2.lab = some label →
      f.key G.graph tcLevel =
        ⟨(f.codes ++ [f.code G.graph]) ++ [codeSentinel], G.graph.relabel label.perm⟩ := by
  intro p hd hp
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  have hl : p.2.2.2.2.lab = v.2.2.lab :=
    (chooseTarget_frame true (.ofGraph G.graph) tcLevel f.level v.1 (recordFirst f.level v.2.1 v.2.2)).1
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hk := h.node.visit_leaf (tcLevel := tcLevel) (fuel := n - f.level) hn h.positive hd (hl ▸ hp)
  have hf : n + 1 - f.level = n - f.level + 1 := by have := h.depth; omega
  rw [Frame.key, hf, hk]
  simp only [prefixKey, List.append_assoc, List.singleton_append]
  rfl

/-- The first leaf's installed native incumbent is the whole frozen
node key. Its code machine is derived from the actual stored prefix and
allocation, without an assumed leaf comparison or key equality. -/
theorem Frame.Valid.first_best {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {f : Frame n}
    (h : f.Valid G) (hs : StoredCodes f.entry.firstcode 1 f.codes)
    (ha : n < f.entry.firstcode.size) (hc : f.entry.canoncode.size = n + 2)
    (hb : ∀ code ∈ f.codes, code < codeSentinel) :
    let p := Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 = n → State.best G.graph (firstterminal f.level p.2.2.2.2) = some (f.key G.graph tcLevel) := by
  intro p hd
  let cs := f.codes ++ [f.code G.graph]
  have hlen : cs.length = f.level := by
    simp only [cs, List.length_append, List.length_singleton, h.length]
  have hstored := h.first_codes (tcLevel := tcLevel) hs ha
  have hcodes : ∀ i, 1 ≤ i → i ≤ cs.length → p.2.2.2.2.firstcode[i]! = cs[i - 1]! := by
    intro i hi hb
    have hh := hstored (i - 1) (by change i - 1 < cs.length; omega)
    simpa only [show 1 + (i - 1) = i by omega] using hh
  have hlt : ∀ code ∈ cs, code < codeSentinel := by
    intro code hcode
    rcases List.mem_append.mp hcode with hm | hm
    · exact hb code hm
    · have he : code = f.code G.graph := List.mem_singleton.mp hm
      rw [he]
      exact f.code_lt G.graph
  have halloc : p.2.2.2.2.canoncode.size = n + 2 := by
    rw [prepareFirst_canoncode]
    exact hc
  have hmachine := firstterminal_codes halloc (by rw [hlen]; exact h.depth) hcodes hlt
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  obtain ⟨label, hlabel⟩ := (h.node.prepare (tcLevel := tcLevel) hn h.positive).1.parse hn
  have hread := Sparse.firstterminal_best (G := G.graph) hmachine
    (by intro he; have := h.positive; simp only [he, List.length_nil] at hlen; omega) hlabel
  rw [hlen, ← h.first_key hd hlabel] at hread
  exact hread

/-- The actual first discrete node installs its prepared leaf and invokes
no sibling continuation. -/
theorem Frame.first_step {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (State n) n)
    (hd : (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).1 = n) :
    Generic.nodeStep (.ofGraph G) tcLevel next true f.level f.numcells f.entry =
      (.unwind (f.level - 1) false, firstterminal f.level
        (Generic.prepareFirst (.ofGraph G) tcLevel f.level f.numcells f.entry).2.2.2.2) := by
  unfold Generic.prepareFirst at hd ⊢
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.chooseTarget, Generic.Policy.firstterminal] at hd ⊢
  simp only [ite_true, hd, beq_self_eq_true, Id.run_pure]

/-- The executed first discrete call satisfies its full maximum contract
from actual code storage and allocation, including a root-level return. -/
theorem Frame.Valid.first_leaf {G : GraphIso.Sparse.Colored n k} {tcLevel fuel : Nat} {f : Frame n}
    (h : f.Valid G) (hs : StoredCodes f.entry.firstcode 1 f.codes)
    (ha : n < f.entry.firstcode.size) (hc : f.entry.canoncode.size = n + 2)
    (hb : ∀ code ∈ f.codes, code < codeSentinel)
    (hd : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1 = n)
    (witness : Nat → Option (Key n) → Prop) :
    let out := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry
    MaxResult (f.key G.graph tcLevel) none (State.best G.graph out.2) (f.level - 1) witness out.1 := by
  dsimp only
  rw [Generic.node, f.first_step _ hd, h.first_best hs ha hc hb hd]
  refine ⟨Bounded.of_eq rfl, Nat.le_refl _, ?_⟩
  simp only [↓reduceIte]
  exact ⟨_, rfl, Key.le_refl _⟩

end Hex.GraphIso.Nauty.Sparse.Max
