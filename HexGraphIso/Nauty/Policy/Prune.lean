/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.Comparison
import all HexGraphIso.Nauty.Policy.Canonical
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Search.Engine

public section

/-! A downward code comparison bounds a whole subtree, including the
ancestors below its first differing code. A code prune retains the
incumbent and returns a comparison machine that recovery can truncate. -/

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- A negative comparison in a code machine has nauty's frozen value. -/
theorem Codes.negative {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon < 0) : st.compCanon = -1 := by
  rcases h.tri with ⟨he, _⟩ | ⟨_, _, _, _, _, _, hd⟩
  · omega
  · rcases hd with ⟨he, _⟩ | ⟨he, _, _⟩ <;> omega

/-- Every extension of a downward-frozen current path is bounded by the incumbent. -/
theorem Codes.prefix_le {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon < 0) (key : Key n) :
    keyLe (prefixKey cs key) (incKey ctx bs st.canonlab) := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := h.negative hc ▸ h
  exact frozen_keyLe hm key

/-- A frozen comparison also bounds every ancestor child below the first
unequal code, independently of any later target choices. -/
theorem Codes.ancestor_le {ctx : Ctx n} {cs bs : List Nat} {st : Search n}
    (h : Codes cs bs st) (hc : st.compCanon < 0) {level : Nat}
    (hlevel : st.eqlevCanon.toNat < level) (hlen : level ≤ cs.length) (key : Key n) :
    keyLe (prefixKey (cs.take level) key) (incKey ctx bs st.canonlab) := by
  have hm : CodeCmpInv n cs bs st.canoncode st.canonlevel st.eqlevCanon (-1) := h.negative hc ▸ h
  exact frozen_take_keyLe hm hlevel hlen key

/-- Once refinement freezes the comparison downward, its entire
specification subtree is bounded, including the newly compared code. -/
theorem Codes.subtree_le {ctx : Ctx n} {stem bs : List Nat} {st : Search n}
    {lab ptn : Array Nat} {active : VSet n} {numcells level : Nat}
    (h : Codes (stem ++ [(refine ctx level lab ptn active numcells).longcode]) bs st)
    (hc : st.compCanon < 0) (tcLevel fuel : Nat) :
    keyLe (prefixKey stem (specNode ctx tcLevel (fuel + 1) level lab ptn active numcells))
      (incKey ctx bs st.canonlab) := by
  obtain ⟨tail, htail⟩ := specNode_codes_head ctx tcLevel fuel level lab ptn active numcells
  let tree := specNode ctx tcLevel (fuel + 1) level lab ptn active numcells
  have hkey := h.prefix_le hc (ctx := ctx) (⟨tail, tree.rows⟩ : Key n)
  have heq : prefixKey stem tree =
      prefixKey (stem ++ [(refine ctx level lab ptn active numcells).longcode])
        (⟨tail, tree.rows⟩ : Key n) := by
    simp only [prefixKey, tree, htail, List.append_assoc, List.singleton_append]
  rw [heq]
  exact hkey

/-- A non-discrete rejected node was rejected by codes before any row comparison. -/
theorem classify_pruned {ctx : Ctx n} {level numcells : Nat} {st : Search n}
    (hnc : numcells ≠ n) (hbad : (classify ctx level numcells st).1 = .bad) :
    st.compCanon < 0 ∧ classify ctx level numcells st = (.bad, st) := by
  rw [classify_eq] at hbad ⊢
  split
  · rename_i hd
    have hc : st.eqlevFirst ≠ level ∧ st.compCanon < 0 := by simpa using hd
    exact ⟨hc.2, rfl⟩
  · rename_i hd
    simp only [hd, bne_iff_ne.mpr hnc, ite_true] at hbad
    cases hbad

/-- Code pruning retains the incumbent and returns a settled machine;
it does not install a key from the unvisited subtree. -/
theorem Comparison.prune {ctx : Ctx n} {cs bs fs : List Nat} {st : Search n} {numcells : Nat}
    (h : Comparison ctx cs bs fs st) (hnc : numcells ≠ n)
    (hbad : (classify ctx cs.length numcells st).1 = .bad) :
    let verdict := classify ctx cs.length numcells st
    let out := (leafExit verdict.1 cs.length verdict.2).2
    Settled cs bs out ∧ FirstCodes cs fs out ∧ out.key ctx bs = st.key ctx bs ∧
      keyLe (incKey ctx fs out.firstlab) (incKey ctx bs out.canonlab) := by
  obtain ⟨hneg, hval⟩ := classify_pruned hnc hbad
  dsimp only
  rw [hval]
  have he := leafExit_canonical .bad cs.length st
  change (leafExit .bad cs.length st).2.canonical = st.canonical at he
  have hs : Settled cs bs st := .codes h.canonical (by omega)
  refine ⟨hs.canonical he, h.first.leaf .bad, key_canonical he, ?_⟩
  have hf := congrArg (fun r => r.2.2) (leafExit_reference .bad cs.length st)
  have hc := congrArg (fun r => r.2.2.2.2.1) he
  change (leafExit .bad cs.length st).2.firstlab = st.firstlab at hf
  change (leafExit .bad cs.length st).2.canonlab = st.canonlab at hc
  rw [hf, hc]
  exact h.lower

end Hex.GraphIso.Nauty.Engine
