/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Comparison
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The exact visit, comparison and target dispatch at an off-path node. -/
@[expose] def prepareOther (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    Nat × Nat × (Int × VSet n × Nat × State n) :=
  let r := visit g level numcells st
  (r.1, r.2.1, chooseTarget false g tcLevel level r.1 (compareCodes level r.2.1 r.2.2))

/-- Off-path preparation extends both histories by its executed code and
retains the incoming semantic native incumbent. -/
theorem Comparison.prepare {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs st) (tcLevel numcells : Nat) (hlen : cs.length ≤ n) :
    let p := prepareOther (.ofGraph G) tcLevel (cs.length + 1) numcells st
    Comparison G (cs ++ [p.2.1]) bs fs p.2.2.2.2.2 ∧
      State.key G bs p.2.2.2.2.2 = State.key G bs st := by
  have hc := refineWith_code_lt (.ofGraph G) (cs.length + 1) st.lab st.ptn
    st.active numcells st.canong.scratch
  change (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).2.1 < codeSentinel at hc
  refine ⟨?_, ?_⟩
  · have hm := ((h.visit (cs.length + 1) numcells).compare hc hlen).target tcLevel
      (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).1
    simpa only [prepareOther, List.length_append, List.length_singleton] using hm
  · unfold prepareOther
    obtain ⟨_, _, _, _, hcan, _⟩ := chooseTarget_codes false (.ofGraph G) tcLevel (cs.length + 1)
      (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).1
      (compareCodes (cs.length + 1) (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).2.1
        (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).2.2)
    have hl := (compareCodes_frame (cs.length + 1)
      (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).2.1
      (Sparse.visit (.ofGraph G) (cs.length + 1) numcells st).2.2).2.2.2
    simp only [State.key, hcan, hl]
    rfl

/-- Native recovery invalidates scratch while retaining both saved labels. -/
theorem recover_labels (inf level : Nat) (st : State n) :
    let out := (policy (n := n)).recover inf level st
    out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  change (recoverLevels level (recoverPtn inf level st)).firstlab = st.firstlab ∧
    (recoverLevels level (recoverPtn inf level st)).canonlab = st.canonlab
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite SearchState.firstlab, apply_ite SearchState.canonlab, ite_self]
  trivial

/-- Restoring a settled code verdict truncates its current path at the
receiving ancestor and retains both reference comparisons and key bound. -/
theorem Comparison.recover {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs st) (hnonpos : st.compCanon ≤ 0) {level : Nat}
    (hlen : level ≤ cs.length) (inf : Nat) :
    Comparison G (cs.take level) bs fs ((policy (n := n)).recover inf level st) := by
  refine ⟨(Settled.codes h.canonical hnonpos).recover hlen inf, ?_, h.nonempty, ?_⟩
  · have hm := recover_firstCodeInv (st := st) (inf := inf) h.first hlen
    rw [← recover_eq] at hm
    exact hm
  · rw [(recover_labels inf level st).1, (recover_labels inf level st).2]
    exact h.lower

theorem recover_key (G : Hex.SparseGraph n) (bs : List Nat) (inf level : Nat) (st : State n) :
    State.key G bs ((policy (n := n)).recover inf level st) = State.key G bs st := by
  simp only [State.key, (recover_labels inf level st).2]

/-- A negative row verdict repurposes `compCanon` after code equality.
Recovery restores the code machine from that equality and retains the
same native key bound and saved first comparison. -/
theorem Comparison.recover_rows {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs { st with compCanon := 0 }) (hnegative : st.compCanon < 0)
    {level : Nat} (hlen : level ≤ cs.length) (inf : Nat) :
    Comparison G (cs.take level) bs fs ((policy (n := n)).recover inf level st) := by
  refine ⟨(Settled.rows (st := st) h.canonical hnegative).recover hlen inf, ?_, h.nonempty, ?_⟩
  · have hm := recover_firstCodeInv (st := st) (inf := inf) h.first hlen
    rw [← recover_eq] at hm
    exact hm
  · rw [(recover_labels inf level st).1, (recover_labels inf level st).2]
    exact h.lower

end Hex.GraphIso.Nauty.Sparse
