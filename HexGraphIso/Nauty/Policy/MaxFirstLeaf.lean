/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.MaxPrepare
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.MaxFrame
import all HexGraphIso.Nauty.Policy.CodeCalls
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.RouteKey
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public import HexGraphIso.Nauty.Policy.MaxNodeTrace
import all HexGraphIso.Nauty.Policy.MaxNodeTrace
import all HexGraphIso.Nauty.Policy.FirstCompare
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.CodeState
import all HexGraphIso.Nauty.Policy.MaxRules
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Invariant.Frame
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Max

variable {n k : Nat}

/-- Installing the first discrete leaf records precisely its frozen
specification key, including the incoming refinement-code prefix. -/
theorem NodeInput.first_best {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel true f bs fs parents)
    (hd : (Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry).1 = n) :
    (firstterminal f.level (Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry).2.2.2.2).best ctx =
      some (f.key ctx tcLevel) := by
  let r := Generic.prepareFirst ctx tcLevel f.level f.numcells f.entry
  let R := f.entry.refined ctx f.level f.numcells
  let codes := f.codes ++ [R.longcode]
  obtain ⟨hp, _, _, _, _, hcanon, hstore, hlt, _, _⟩ := h.entry
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hlength : codes.length = f.level := by
    simp only [codes, List.length_append, List.length_singleton, h.frame.length]
  have hnonempty : codes ≠ [] := by simp [codes]
  have hstored := hp.code_prefix (tcLevel := tcLevel) h.frame.length hstore
  have hvalues : ∀ i, 1 ≤ i → i ≤ codes.length → r.2.2.2.2.firstcode[i]! = codes[i - 1]! := by
    intro i hi hb
    have hs := hstored (i - 1) (by change i - 1 < codes.length; omega)
    simpa only [show 1 + (i - 1) = i by omega] using hs
  have hcsize : r.2.2.2.2.canoncode.size = n + 2 := by
    rw [prepareFirst_canoncode, hcanon]
  have hcodeslt : ∀ c ∈ codes, c < codeSentinel := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hlt c hc
    · rw [List.mem_singleton.mp hc]
      exact refine_longcode_lt ctx f.level f.entry.lab f.entry.ptn f.entry.active f.numcells
  have hbest := firstterminal_best (ctx := ctx) hnonempty hcsize
    (by rw [hlength]; exact h.frame.depth) hvalues hcodeslt
  rw [hlength] at hbest
  have hdisc : discreteAt R.ptn f.level n = true := by
    apply (refine_discrete_iff hn0 h.frame.partition h.frame.positive).mp
    exact hd
  have hl := (prepareFirst_fields ctx tcLevel f.level f.numcells f.entry).1
  change r.2.2.2.2.lab = R.lab at hl
  change discreteAt (refine ctx f.level f.entry.lab f.entry.ptn f.entry.active f.numcells).ptn f.level n = true at hdisc
  have hkey : f.key ctx tcLevel = pathLeafKey ctx codes r.2.2.2.2.lab := by
    have hdepth := h.frame.depth
    rw [Frame.key, show n + 1 - f.level = n - f.level + 1 by omega]
    simp only [specNode, hdisc, ↓reduceIte, prefixKey, pathLeafKey, codes, List.append_assoc, hl]
    rfl
  rw [hkey]
  exact hbest

/-- The first discrete branch completes the node without invoking its
sweep continuation. -/
theorem first_leaf (G : Colored n k) (tcLevel : Nat) :
    NodeRule G tcLevel true (fun level numcells st =>
      (Generic.prepareFirst { g := rowsOf G } tcLevel level numcells st).1 = n) := by
  intro fuel _ level numcells st hd cs bs fs parents h
  let f : Frame n := ⟨level, numcells, cs, st⟩
  rw [f.first_step _ hd, h.first_best hd]
  have hb : bs = [] := h.entry.2.1
  rw [hb]
  change Generic.Result (f.key { g := rowsOf G } tcLevel) none
    (some (f.key { g := rowsOf G } tcLevel)) (level - 1) _ (.unwind (level - 1) false)
  exact ⟨Generic.Bounded.of_eq rfl, Nat.le_refl _, by
    simp only [↓reduceIte]
    exact ⟨_, rfl, keyLe_refl _⟩⟩

end Hex.GraphIso.Nauty.Max
