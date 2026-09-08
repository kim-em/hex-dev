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

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- An actual discrete off-path emission installs the maximum of its
incoming semantic incumbent and its full frozen node key. -/
theorem NodeInput.leaf_best {G : Colored n k} {ctx : Ctx n} {tcLevel fuel : Nat}
    {f : Frame n} {bs fs : List Nat} {parents : Parents n}
    (h : NodeInput G ctx tcLevel fuel false f bs fs parents)
    (hd : (prepareOther ctx tcLevel f.level f.numcells f.entry).1 = n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false) :
    let p := prepareOther ctx tcLevel f.level f.numcells f.entry
    let c := classify ctx f.level p.1 p.2.2.2.2.2
    (leafExit c.1 f.level c.2).2.best ctx =
      some (incMax (f.entry.key ctx bs) (f.key ctx tcLevel)) := by
  let p := prepareOther ctx tcLevel f.level f.numcells f.entry
  let r := f.entry.refined ctx f.level f.numcells
  have hn0 : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hlen := h.frame.length
  have hdepth := h.frame.depth
  obtain ⟨hin, hc⟩ := h.entry
  obtain ⟨hok, hi, hh, _, _⟩ := hin.prepare hn0 hgsz hsymm hloop
  have hm := hc.prepare (tcLevel := tcLevel) (numcells := f.numcells) (by omega)
  simp only [hlen] at hm
  have hlength : (f.codes ++ [p.2.1]).length = f.level := by simp only [List.length_append,
    List.length_singleton, hlen]
  have hcomparison : Comparison ctx (f.codes ++ [p.2.1]) bs fs p.2.2.2.2.2 := hm.1
  have hhistory : History ctx tcLevel (f.codes ++ [p.2.1]).length
      (f.codes ++ [p.2.1]).length n p.2.2.2.2.2 := by
    simpa only [hlength, hd] using hh
  have hpartition : SearchOk G (f.codes ++ [p.2.1]).length n p.2.2.2.2.2.view := by
    simpa only [hlength, hd] using hok
  have hbest := hhistory.leaf_best hi hn0 (by rw [hlength]; exact h.frame.positive)
    hpartition hcomparison.canonical hcomparison.first hcomparison.nonempty hcomparison.lower
    hgsz hsymm hloop
  rw [hlength] at hbest
  have hl : p.2.2.2.2.2.lab = r.lab := by
    dsimp only [p, prepareOther]
    rw [chooseTarget_fields]
    exact (compareCodes_frame _ _ _).1
  have hp : p.2.2.2.2.2.ptn = r.ptn := by
    dsimp only [p, prepareOther]
    rw [chooseTarget_fields]
    exact (compareCodes_frame _ _ _).2.1
  have hdisc : discreteAt r.ptn f.level n = true := by
    have he := searchOk_end hn0 hok h.frame.positive
    have hs := hok.ptnSize
    have hn := hok.count
    change p.1 = bcount p.2.2.2.2.2.ptn f.level n at hn
    change p.2.2.2.2.2.ptn.size = n at hs
    change p.2.2.2.2.2.ptn[p.2.2.2.2.2.ptn.size - 1]! ≤ f.level at he
    rw [hp] at hs he hn
    apply (discreteAt_iff_bcount hs.symm he).mpr
    exact hn.symm.trans hd
  have hkey : f.key ctx tcLevel = pathLeafKey ctx (f.codes ++ [p.2.1]) p.2.2.2.2.2.lab := by
    change discreteAt (refine ctx f.level f.entry.lab f.entry.ptn f.entry.active f.numcells).ptn
      f.level n = true at hdisc
    change p.2.2.2.2.2.lab =
      (refine ctx f.level f.entry.lab f.entry.ptn f.entry.active f.numcells).lab at hl
    rw [Frame.key, show n + 1 - f.level = n - f.level + 1 by omega]
    simp only [specNode, hdisc, ↓reduceIte, prefixKey, pathLeafKey, List.append_assoc, hl]
    rfl
  dsimp only
  rw [hd, hbest, ← hkey]
  exact congrArg (fun best => some (incMax best (f.key ctx tcLevel))) hm.2

end Hex.GraphIso.Nauty.Engine.Max
