/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstCodes
public import HexGraphIso.Nauty.Policy.Effect
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Both production code comparisons and the saved first leaf's lower
bound on the native incumbent. The labels are parsed from actual storage. -/
structure Comparison (G : Hex.SparseGraph n) (cs bs fs : List Nat) (st : State n) : Prop where
  canonical : Codes cs bs st
  first : FirstCodeInv n cs fs st.firstcode st.eqlevFirst
  nonempty : bs ≠ []
  lower : ∃ f c : Label n, Label.ofArray? n st.firstlab = some f ∧
    Label.ofArray? n st.canonlab = some c ∧
    Key.Le ⟨fs ++ [codeSentinel], G.relabel f.perm⟩ ⟨bs ++ [codeSentinel], G.relabel c.perm⟩

namespace Comparison

variable {G : Hex.SparseGraph n} {cs bs fs : List Nat} {st : State n}

/-- Updates outside the two comparisons and saved labels preserve meaning. -/
theorem congr (h : Comparison G cs bs fs st) {out : State n}
    (hcc : out.canoncode = st.canoncode) (hcl : out.canonlevel = st.canonlevel)
    (hce : out.eqlevCanon = st.eqlevCanon) (hcmp : out.compCanon = st.compCanon)
    (hfc : out.firstcode = st.firstcode) (hfe : out.eqlevFirst = st.eqlevFirst)
    (hfl : out.firstlab = st.firstlab) (hcan : out.canonlab = st.canonlab) :
    Comparison G cs bs fs out := by
  refine ⟨?_, ?_, h.nonempty, ?_⟩
  · change CodeCmpInv n cs bs _ _ _ _
    rw [hcc, hcl, hce, hcmp]
    exact h.canonical
  · rw [hfc, hfe]
    exact h.first
  · rw [hfl, hcan]
    exact h.lower

theorem visit (h : Comparison G cs bs fs st) (level numcells : Nat) :
    Comparison G cs bs fs (Sparse.visit (.ofGraph G) level numcells st).2.2 :=
  h.congr rfl rfl rfl rfl rfl rfl rfl rfl

/-- The executed next code advances both path comparisons. -/
theorem compare (h : Comparison G cs bs fs st) {code : Nat}
    (hc : code < codeSentinel) (hlen : cs.length ≤ n) :
    Comparison G (cs ++ [code]) bs fs (compareCodes (cs.length + 1) code st) := by
  refine ⟨h.canonical.compare hc hlen, compareCodes_firstCodeInv h.first hc, h.nonempty, ?_⟩
  obtain ⟨_, _, hf, hcan⟩ := compareCodes_frame (cs.length + 1) code st
  rw [hf, hcan]
  exact h.lower

/-- Native target selection retains the incumbent and may lower only
agreement with the first path when a stored hint disagrees. -/
theorem target (h : Comparison G cs bs fs st) (tcLevel numcells : Nat) :
    Comparison G cs bs fs (chooseTarget false (.ofGraph G) tcLevel cs.length numcells st).2.2.2 := by
  obtain ⟨hcc, hcl, hce, hcmp, hcan, hfl⟩ :=
    chooseTarget_codes false (.ofGraph G) tcLevel cs.length numcells st
  have hf := congrArg Prod.fst (chooseTarget_reference (.ofGraph G) tcLevel cs.length numcells st)
  change (chooseTarget false (.ofGraph G) tcLevel cs.length numcells st).2.2.2.firstcode = st.firstcode at hf
  refine ⟨?_, ?_, h.nonempty, ?_⟩
  · change CodeCmpInv n cs bs _ _ _ _
    rw [hcc, hcl, hce, hcmp]
    exact h.canonical
  · rw [hf]
    exact firstCodeInv_mono h.first (chooseTarget_le (.ofGraph G) tcLevel cs.length numcells st)
  · rw [hfl, hcan]
    exact h.lower

theorem child (h : Comparison G cs bs fs st) (first : Bool) (level tc tv : Nat) :
    Comparison G cs bs fs ((policy (n := n)).child first level tc tv st) := by
  cases first <;> exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl

theorem cheap (h : Comparison G cs bs fs st) (first : Bool) (level : Nat) :
    Comparison G cs bs fs (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl rfl rfl rfl rfl rfl rfl

/-- Initialized code machines at the first leaf have a parsed incumbent
equal to the first reference, so the required key lower bound is reflexive. -/
theorem firstterminal {cs : List Nat} {st : State n} {l : Label n}
    (hc : Codes cs cs (Nauty.firstterminal cs.length st))
    (hf : FirstCodeInv n cs cs (Nauty.firstterminal cs.length st).firstcode
      (Nauty.firstterminal cs.length st).eqlevFirst)
    (hne : cs ≠ []) (hl : Label.ofArray? n st.lab = some l) :
    Comparison G cs cs cs (Nauty.firstterminal cs.length st) := by
  refine ⟨hc, hf, hne, l, l, ?_, ?_, Key.le_refl _⟩
  all_goals unfold Nauty.firstterminal; exact hl

end Comparison

/-- The initialized native search supplies both comparisons and the first
key bound at its actual first leaf, with no leaf invariant premise. -/
theorem initial_comparison (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    ∃ last leaf codes,
      Generic.FirstPath (.ofGraph G.graph) 100 (n + 2) 1 p.2.length
        (initial (.ofGraph G.graph) p.1 p.2) last leaf ∧
      codes.length = last ∧ Comparison G.graph codes codes codes (Nauty.firstterminal last leaf) := by
  obtain ⟨last, leaf, codes, l, hp, hlen, hne, hl, hc, hf, _⟩ := initial_codes G hn
  refine ⟨last, leaf, codes, hp, hlen, ?_⟩
  rw [← hlen] at hc hf ⊢
  exact Comparison.firstterminal hc hf hne hl

end Hex.GraphIso.Nauty.Sparse
