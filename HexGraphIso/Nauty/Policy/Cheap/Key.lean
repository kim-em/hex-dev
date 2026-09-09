/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Key
public import HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The refinement codes and terminal rows along an individualization path. -/
def pathKey (ctx : Ctx n) : Nat → RefineSt n → List (Nat × Nat) → Key n
  | _, st, [] => ⟨[st.longcode, codeSentinel], leafRows ctx st.lab⟩
  | level, st, (tc, o) :: path =>
      prefixKey [st.longcode]
        (pathKey ctx (level + 1) (childSt ctx level st tc st.lab[tc + o]!) path)

/-- The key stores the descent's real refinement codes followed by its sentinel. -/
theorem pathKey_codes (ctx : Ctx n) (path : List (Nat × Nat))
    (level : Nat) (st : RefineSt n) :
    (pathKey ctx level st path).codes = pathCodes ctx level st path ++ [codeSentinel] := by
  induction path generalizing level st with
  | nil => rfl
  | cons a path ih =>
    obtain ⟨tc, o⟩ := a
    simp only [pathKey, pathCodes, prefixKey, ih, List.cons_append, List.nil_append]

/-- Any complete selected descent below a small-cell node realizes its
entire specification maximum, including every refinement code. -/
theorem SubtreeOk.path_key {ctx : Ctx n}
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (path : List (Nat × Nat)) :
    ∀ {lab ptn : Array Nat} {active : VSet n} {tcLevel fuel level numcells last : Nat}
      {leaf : RefineSt n},
      let r := refine ctx level lab ptn active numcells
      SubtreeOk ctx level r → DescPath ctx level r path last leaf →
      Selects ctx tcLevel level r path → discreteAt leaf.ptn last n = true →
      path.length < fuel → level + fuel ≤ n + 1 →
      specNode ctx tcLevel fuel level lab ptn active numcells = pathKey ctx level r path := by
  induction path with
  | nil =>
    intro lab ptn active tcLevel fuel level numcells last leaf r hS hp hs hd hf hb
    obtain ⟨rfl, rfl⟩ := descPath_nil hp
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp only [specNode, hd, ite_true, pathKey, r]
  | cons a path ih =>
    obtain ⟨tc, o⟩ := a
    intro lab ptn active tcLevel fuel level numcells last leaf r hS hp hs hd hf hb
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
    cases hp with
    | step _ e _ hlvl hcell hne ho htail =>
    have he := target_end_lt hS.it.ok.ptnSize hS.it.ok.ptnEnd hcell
    have hic := cells_isCell (Nat.le_of_eq hS.it.ok.ptnSize.symm) hS.it.ok.ptnEnd _ hcell
    have hce := cellEnd_of_isCell hic (by omega) (by rw [hS.it.ok.ptnSize]; omega)
    have htc : specTargetcell ctx r.lab r.ptn level tcLevel = tc := hs.1
    have ht : specMaketargetcell ctx r.lab r.ptn level tcLevel =
        (tc, worksetOf n r.lab tc e, e - tc + 1) := by
      change cellEnd r.ptn level (tc + 1) = tc + (e + 1 - tc) - 1 at hce
      rw [show tc + (e + 1 - tc) - 1 = e by omega] at hce
      simp only [specMaketargetcell, htc, hce]
    have hn : discreteAt r.ptn level n = false := by
      rw [discreteAt, List.all_eq_false]
      exact ⟨(tc, e), hcell, by simpa using (Nat.ne_of_lt hne)⟩
    have hm := hS.node_key hgsz hsymm hloop hn (o := o)
      (by change o < (specMaketargetcell ctx r.lab r.ptn level tcLevel).2.2; simp only [ht]; omega)
      (by omega : level + 1 + fuel ≤ n + 1) []
    have hchild := subtreeOk_child hS hlvl hsymm hcell hne ho
    have hc := ih hchild htail hs.2 hd (by simpa using hf) (by omega)
    change specNode ctx tcLevel fuel (level + 1)
      (breakout n r.lab r.ptn (level + 1) tc r.lab[tc + o]!).1
      (r.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (r.numcells + 1) = _ at hc
    change specNode ctx tcLevel (fuel + 1) level lab ptn active numcells =
      prefixKey [r.longcode] (pathKey ctx (level + 1)
        (childSt ctx level r tc r.lab[tc + o]!) path)
    have hm' : specNode ctx tcLevel (fuel + 1) level lab ptn active numcells =
        prefixKey [r.longcode] (childKey ctx tcLevel fuel level r.lab r.ptn tc r.numcells o) := by
      dsimp only [r] at ht
      simpa only [r, ht, prefixKey, List.nil_append, key_eta] using hm
    rw [hm']
    exact congrArg (prefixKey [r.longcode]) hc

end Hex.GraphIso.Nauty
