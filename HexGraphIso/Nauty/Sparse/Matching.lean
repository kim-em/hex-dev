/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstRef
public import HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

namespace Generation

/-- Literal matching with the stored native first reference, including
the sentinel and the parsed first label's normalized sparse graph. -/
structure Matches (G : Hex.SparseGraph n) (level : Nat) (st : State n)
    (targets : List Nat) (key : Key n) : Prop where
  codes : StoredCodes st.firstcode level key.codes
  targets : Targets st.firsttc level targets
  graph : ∃ label, Label.ofArray? n st.firstlab = some label ∧ key.graph = G.relabel label.perm

namespace Matches

variable {G : Hex.SparseGraph n} {level : Nat} {st out : State n}
  {targets : List Nat} {key : Key n}

theorem congr (h : Matches G level st targets key) (he : out.reference = st.reference) :
    Matches G level out targets key := by
  have hc := congrArg (fun r : Array Nat × Array Int × Array Nat => r.1) he
  have ht := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.1) he
  have hl := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2) he
  change out.firstcode = st.firstcode at hc
  change out.firsttc = st.firsttc at ht
  change out.firstlab = st.firstlab at hl
  exact ⟨by rw [hc]; exact h.codes, by rw [ht]; exact h.targets, by rw [hl]; exact h.graph⟩

theorem tail {tc code : Nat} (h : Matches G level st (tc :: targets) ⟨code :: key.codes, key.graph⟩) :
    Matches G (level + 1) st targets key := by
  refine ⟨?_, ?_, h.graph⟩
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.codes (i + 1) (by simp; omega)
  · intro i hi
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h.targets (i + 1) (by simp; omega)

theorem cons {tc code : Nat} (h : Matches G (level + 1) st targets key)
    (hc : st.firstcode[level]! = code) (ht : st.firsttc[level]! = Int.ofNat tc) :
    Matches G level st (tc :: targets) ⟨code :: key.codes, key.graph⟩ := by
  refine ⟨StoredCodes.cons hc h.codes, ?_, h.graph⟩
  intro i hi
  cases i with
  | zero => simpa using ht
  | succ i =>
    simpa only [List.getElem!_cons_succ, show level + (i + 1) = level + 1 + i by omega]
      using h.targets i (by simpa using hi)

/-- A matching selected occurrence identifies the stored current code
and, when open, the stored native unhinted target. -/
theorem head {tcLevel : Nat} {root : RefineSt n}
    (h : Matches G level st targets key) (ho : HasLeaf G tcLevel level root targets key) :
    st.firstcode[level]! = root.longcode ∧
      (discreteAt root.ptn level n ≠ true →
        st.firsttc[level]! = Int.ofNat (targetcell (.ofGraph G) root.lab root.ptn level tcLevel (-1))) := by
  rcases ho.cases with ⟨label, hd, hp, rfl, rfl⟩ |
    ⟨tc, len, o, scratch, rest, tail, hc, hb, hn, hoff, hs, ht, hchild, rfl, rfl⟩
  · refine ⟨?_, fun hopen => (hopen hd).elim⟩
    simpa using h.codes 0 (by simp)
  · refine ⟨?_, fun _ => ?_⟩
    · simpa using h.codes 0 (by simp)
    · simpa only [Nat.add_zero, List.getElem!_cons_zero, ht] using h.targets 0 (by simp)

end Matches
end Generation

/-- The saved selected first descent occurs with exactly its stored
target/code chain and parsed first-reference graph. -/
theorem FirstRef.occurs {G : Hex.SparseGraph n} {tcLevel level : Nat}
    {root : RefineSt n} {st : State n} (h : FirstRef G tcLevel level root st)
    (hr : RefineSt.Ready G level root) :
    ∃ targets key, Generation.HasLeaf G tcLevel level root targets key ∧
      Generation.Matches G level st targets key := by
  have hleaf := h.trace.descent.ready hr
  obtain ⟨label, hparse⟩ := Label.ofArray?_exists hleaf.spec.label
  refine ⟨h.path.map Prod.fst, ⟨h.codes ++ [codeSentinel], G.relabel label.perm⟩,
    ⟨h.last, h.leaf, h.path, h.codes, h.trace, h.selects, h.discrete, label, hparse, rfl, rfl⟩,
    ⟨?_, h.targets, ⟨label, ?_, rfl⟩⟩⟩
  · intro i hi
    by_cases hb : i < h.codes.length
    · rw [getElem!_append_left hb]
      exact h.stored i hb
    · have he : i = h.codes.length := by
        change i < (h.codes ++ [codeSentinel]).length at hi
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      have hlength : level + h.codes.length = h.last + 1 := by
        have hp := h.trace.descent.length
        have hc := h.trace.length
        omega
      rw [hlength, h.sentinel]
      simp
  · rw [← h.lab]
    exact hparse

end Hex.GraphIso.Nauty.Sparse
