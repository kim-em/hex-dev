/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFrame
public import HexGraphIso.Nauty.Sparse.LeafBound
public import HexGraphIso.Nauty.Sparse.CodeState
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.ReturnCodes
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The exact off-path preparation, classification and native leaf exit. -/
def Frame.emit (G : Hex.SparseGraph n) (tcLevel : Nat) (f : Frame n) : Exit × State n :=
  let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
  let c := classify (.ofGraph G) f.level p.1 p.2.2.2.2.2
  leafExit c.1 f.level c.2

/-- A terminal emission is the actual native node step; it invokes no sibling continuation. -/
theorem Frame.emit_step {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (State n) n) (h : (f.emit G tcLevel).1 ≠ .done) :
    Generic.nodeStep (.ofGraph G) tcLevel next false f.level f.numcells f.entry = f.emit G tcLevel := by
  unfold Frame.emit at h ⊢
  dsimp only [prepareOther] at h ⊢
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hv : visit (.ofGraph G) f.level f.numcells f.entry = v at h ⊢
  obtain ⟨nc, code, st⟩ := v
  simp only [Bool.false_eq_true, ite_false]
  generalize ht : chooseTarget false (.ofGraph G) tcLevel f.level nc (compareCodes f.level code st) = t at h ⊢
  obtain ⟨tc, cell, len, out⟩ := t
  generalize hc : leafExit (classify (.ofGraph G) f.level nc out).1 f.level
    (classify (.ofGraph G) f.level nc out).2 = c at h ⊢
  obtain ⟨exit, result⟩ := c
  cases exit with
  | done => exact (h rfl).elim
  | fuel => rfl
  | unwind target short => rfl

/-- When the native dispatch continues, its remaining computation is
exactly the target sweep followed by the native completion bookkeeping. -/
theorem Frame.sweep_step {G : Hex.SparseGraph n} {tcLevel : Nat} {f : Frame n}
    (next : Generic.SweepFn (State n) n) (h : (f.emit G tcLevel).1 = .done) :
    Generic.nodeStep (.ofGraph G) tcLevel next false f.level f.numcells f.entry =
      let p := prepareOther (.ofGraph G) tcLevel f.level f.numcells f.entry
      let s := next false f.level p.1 p.2.2.1.toNat
        ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
        (cheapCheck false f.level (f.emit G tcLevel).2)
      match s.1 with
      | .done => (.unwind (f.level - 1) false,
          (policy (n := n)).afterSweep false f.level p.2.2.2.2.1 s.2.1 s.2.2)
      | _ => (s.1, s.2.2) := by
  unfold Frame.emit at h ⊢
  dsimp only [prepareOther] at h ⊢
  unfold Generic.nodeStep
  dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
    Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.classify,
    Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
  generalize hv : visit (.ofGraph G) f.level f.numcells f.entry = v at h ⊢
  obtain ⟨nc, code, st⟩ := v
  simp only [Bool.false_eq_true, ite_false]
  generalize ht : chooseTarget false (.ofGraph G) tcLevel f.level nc (compareCodes f.level code st) = t at h ⊢
  obtain ⟨tc, cell, len, out⟩ := t
  generalize hc : leafExit (classify (.ofGraph G) f.level nc out).1 f.level
    (classify (.ofGraph G) f.level nc out).2 = c at h ⊢
  obtain ⟨exit, result⟩ := c
  cases h
  rfl

/-- A discrete prepared native label gives the whole frozen node key,
including its ancestor codes and terminal sentinel. -/
theorem Frame.Valid.leaf_key {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {label : Label n} (h : f.Valid G) :
    let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 = n → Label.ofArray? n p.2.2.2.2.2.lab = some label →
      f.key G.graph tcLevel =
        ⟨(f.codes ++ [p.2.1]) ++ [codeSentinel], G.graph.relabel label.perm⟩ := by
  intro p hd hp
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  have hlabel : p.2.2.2.2.2.lab = v.2.2.lab :=
    (chooseTarget_frame false (.ofGraph G.graph) tcLevel f.level v.1
      (compareCodes f.level v.2.1 v.2.2)).1.trans (compareCodes_frame f.level v.2.1 v.2.2).1
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hk := h.node.visit_leaf (tcLevel := tcLevel) (fuel := n - f.level) hn h.positive hd
    (hlabel ▸ hp)
  have hf : n + 1 - f.level = n - f.level + 1 := by have := h.depth; omega
  rw [Frame.key, hf, hk]
  simp only [prefixKey, List.append_assoc, List.singleton_append]
  rfl

/-- Every actual discrete classifier, including both automorphism branches,
returns the exact permitted maximum for the complete frozen node. -/
theorem Frame.Valid.leaf_bound {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} (h : f.Valid G)
    (hi : CodeEntry G tcLevel f.level f.numcells f.entry)
    (hc : Comparison G.graph f.codes bs fs f.entry)
    (hd : (prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).1 = n) :
    ∃ bs', ReturnCodes G.graph f.codes bs' fs (f.emit G.graph tcLevel).2 ∧
      Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry) (State.best G.graph (f.emit G.graph tcLevel).2) ∧
      Covers (f.key G.graph tcLevel) (State.best G.graph (f.emit G.graph tcLevel).2) := by
  let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hlen := h.length
  have hdepth := h.depth
  have hm := hc.prepare tcLevel f.numcells (by omega)
  rw [hlen] at hm
  have hr := hi.prepare hn h.positive
  have hlength : (f.codes ++ [p.2.1]).length = f.level := by
    simp only [List.length_append, List.length_singleton, hlen]
  obtain ⟨bs', label, hp, hcodes, hb, hcover⟩ := hm.1.leaf_bounded (tcLevel := tcLevel)
    (by simpa only [List.length_append, List.length_singleton, hlen, hd] using hr.route)
    (by simpa only [List.length_append, List.length_singleton, hlen, hd] using hr.toTraceReady)
    hn (by simpa only [List.length_append, List.length_singleton, hlen] using h.positive)
  simp only [List.length_append, List.length_singleton, hlen] at hcodes hb hcover
  have hout : (leafExit (classify (.ofGraph G.graph) f.level n p.2.2.2.2.2).1 f.level
      (classify (.ofGraph G.graph) f.level n p.2.2.2.2.2).2).2 = (f.emit G.graph tcLevel).2 := by
    unfold Frame.emit
    change _ = (leafExit (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 f.level
      (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).2).2
    rw [hd]
  rw [hout] at hcodes hb hcover
  have hkey := h.leaf_key hd hp
  rw [← hkey, hm.2] at hb
  rw [← hkey] at hcover
  rw [← hcodes.read] at hb hcover
  exact ⟨bs', hcodes.prefix ⟨[p.2.1], rfl⟩, hb, hcover⟩

/-- Nonterminal native rejection covers the complete node while retaining
the incoming incumbent. Its negative code verdict is derived from the
actual classifier, including the saved first-reference admission test. -/
theorem Frame.Valid.prune_bound {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs fs : List Nat} (h : f.Valid G)
    (hc : Comparison G.graph f.codes bs fs f.entry) :
    let p := prepareOther (.ofGraph G.graph) tcLevel f.level f.numcells f.entry
    p.1 ≠ n → (classify (.ofGraph G.graph) f.level p.1 p.2.2.2.2.2).1 = .bad →
      ReturnCodes G.graph f.codes bs fs (f.emit G.graph tcLevel).2 ∧
      Bounded (f.key G.graph tcLevel) (State.key G.graph bs f.entry) (State.best G.graph (f.emit G.graph tcLevel).2) ∧
      Covers (f.key G.graph tcLevel) (State.best G.graph (f.emit G.graph tcLevel).2) := by
  intro p hd hbad
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  have hlen := h.length
  have hdepth := h.depth
  have hm := hc.prepare tcLevel f.numcells (by omega)
  rw [hlen] at hm
  have hlength : (f.codes ++ [p.2.1]).length = f.level := by
    simp only [List.length_append, List.length_singleton, hlen]
  have hbad' : (classify (.ofGraph G.graph) (f.codes ++ [p.2.1]).length p.1 p.2.2.2.2.2).1 = .bad := by
    rw [hlength]
    exact hbad
  have hr := hm.1.prune_returned hd hbad'
  simp only [List.length_append, List.length_singleton, hlen] at hr
  have hneg : p.2.2.2.2.2.compCanon < 0 := by
    rw [classify_eq] at hbad
    split at hbad
    · rename_i hb
      exact (show p.2.2.2.2.2.eqlevFirst ≠ f.level ∧ p.2.2.2.2.2.compCanon < 0 by simpa using hb).2
    · simp only [bne_iff_ne.mpr hd, ite_true] at hbad
      contradiction
  have hcount := h.node.spec.depth
  have hcover := h.node.code_cover (tcLevel := tcLevel) (fuel := n - f.level) hn h.positive
    (by omega) hm.1 hneg
  have hf : n + 1 - f.level = n - f.level + 1 := by omega
  have hread : State.best G.graph (f.emit G.graph tcLevel).2 = State.key G.graph bs f.entry :=
    hr.1.read.trans (hr.2.trans hm.2)
  refine ⟨hr.1.prefix ⟨[p.2.1], rfl⟩, ?_, ?_⟩
  · rw [hread]
    exact Bounded.refl _ _
  · rw [hread, ← hm.2, Frame.key, hf]
    exact hcover

end Hex.GraphIso.Nauty.Sparse.Max
