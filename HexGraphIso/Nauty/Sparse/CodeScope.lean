/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.Coverage
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A frozen negative code comparison covers every continuation of any
ancestor prefix that already contains its first divergent code. -/
theorem Comparison.ancestor_cover {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}
    (h : Comparison G cs bs fs st) (hneg : st.compCanon < 0) {length : Nat}
    (hdiv : st.eqlevCanon.toNat < length) (hlen : length ≤ cs.length) (tail : Key n) :
    Covers (prefixKey (cs.take length) tail) (State.key G bs st) := by
  have hcomp : st.compCanon = -1 := by
    rcases h.canonical.tri with ⟨he, _⟩ | ⟨_, _, _, _, _, _, he⟩
    · omega
    · rcases he with ⟨he, _⟩ | ⟨he, _, _⟩ <;> omega
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := hcomp ▸ h.canonical
  obtain ⟨_, canon, _, hcanon, _⟩ := h.lower
  refine ⟨⟨bs ++ [codeSentinel], G.relabel canon.perm⟩, ?_, ?_⟩
  · simp only [State.key, h.nonempty, ite_false, hcanon, Option.map_some]
  · have hh := codeInv_take_listCmp_lt hm hdiv hlen tail.codes
    rw [codes_compare] at hh
    change (Key.cmp ⟨cs.take length ++ tail.codes, tail.graph⟩
      ⟨bs ++ [codeSentinel], G.relabel canon.perm⟩).isLE = true
    simp only [Key.cmp, hh, Ordering.then]
    rfl

namespace Max

/-- Each recorded ancestor code has its original valid native entry.
This invariant stores syntax and geometry, not a maximum-correctness premise. -/
def CodeScope (G : GraphIso.Sparse.Colored n k) (cs : List Nat) (frames : Frames n) : Prop :=
  ∀ target, target < cs.length → ∃ f, frames target = some f ∧ f.Valid G ∧
    f.level = target + 1 ∧ f.codes ++ [f.code G.graph] = cs.take (target + 1)

theorem CodeScope.root (G : GraphIso.Sparse.Colored n k) : CodeScope G [] (fun _ => none) := by
  intro target ht
  cases ht

/-- Entering an actual child adds its parent's entry and exact cached
visit code. Every earlier ancestor keeps the same recorded prefix. -/
theorem CodeScope.push {G : GraphIso.Sparse.Colored n k} {f : Frame n} {frames : Frames n}
    (h : CodeScope G f.codes frames) (hf : f.Valid G) :
    CodeScope G (f.codes ++ [f.code G.graph]) (frames.insert f) := by
  intro target ht
  have hlen := hf.length
  simp only [List.length_append, List.length_singleton] at ht
  by_cases he : target = f.codes.length
  · subst target
    refine ⟨f, ?_, hf, hlen.symm, ?_⟩
    · simp only [Frames.insert, show f.codes.length = f.level - 1 by omega, ↓reduceIte]
    · rw [List.take_of_length_le (by simp)]
  · have hlt : target < f.codes.length := by omega
    obtain ⟨a, ha, hv, hl, hp⟩ := h target hlt
    refine ⟨a, ?_, hv, hl, ?_⟩
    · simpa only [Frames.insert, ite_eq_right (by omega : target ≠ f.level - 1)] using ha
    · rw [List.take_append, show target + 1 - f.codes.length = 0 by omega,
        List.take_zero, List.append_nil]
      exact hp

/-- Recovery to a shorter already-recorded path retains its ancestor entries. -/
theorem CodeScope.take {G : GraphIso.Sparse.Colored n k} {cs : List Nat} {frames : Frames n}
    (h : CodeScope G cs frames) (length : Nat) : CodeScope G (cs.take length) frames := by
  intro target ht
  have hlength : target < min length cs.length := by simpa only [List.length_take] using ht
  obtain ⟨f, hf, hv, hl, hp⟩ := h target (by omega)
  refine ⟨f, hf, hv, hl, ?_⟩
  rw [List.take_take, Nat.min_eq_left (by omega)]
  exact hp

/-- A prefix rejection resolves the actual frozen frame at its named
receiving level, including the root entry at target zero. -/
theorem CodeScope.witness {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {cs : List Nat} {frames : Frames n} {best : Option (Key n)}
    (h : CodeScope G cs frames) (ht : target < cs.length)
    (hc : ∀ tail : Key n, Covers (prefixKey (cs.take (target + 1)) tail) best) :
    Witness G tcLevel frames target best := by
  obtain ⟨f, hf, hv, _, hp⟩ := h target ht
  refine ⟨f, hf, hv, Or.inr ?_⟩
  intro tail
  rw [hp]
  exact hc tail

/-- The executed comparison supplies its nonlocal code-return witness.
Only the recorded prefix and the literal divergence level are required. -/
theorem CodeScope.rejected {G : GraphIso.Sparse.Colored n k} {tcLevel target : Nat}
    {cs bs fs : List Nat} {frames : Frames n} {st : State n}
    (h : CodeScope G cs frames) (ht : target < cs.length)
    (hc : Comparison G.graph cs bs fs st) (hneg : st.compCanon < 0)
    (hdiv : st.eqlevCanon.toNat ≤ target) :
    Witness G tcLevel frames target (State.key G.graph bs st) :=
  h.witness ht (fun tail => hc.ancestor_cover hneg (by omega) (by omega) tail)

end Max
end Hex.GraphIso.Nauty.Sparse
