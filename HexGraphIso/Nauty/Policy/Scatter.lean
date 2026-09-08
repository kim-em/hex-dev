/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Search
public import HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Store

public section

/-!
The engine's reusable permutation workspace has the same scatter
equations as a fresh workspace. The previous entries are irrelevant
when the reference labelling is a permutation.
-/

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

private theorem forIn_fold (f : Nat → Array Nat → Array Nat) :
    ∀ (xs : List Nat) (a : Array Nat),
      (forIn xs a (fun i b => pure (.yield (f i b))) : Id (Array Nat)) =
        xs.foldl (fun b i => f i b) a
  | [], _ => rfl
  | i :: xs, a => by
    rw [List.forIn_cons]
    exact forIn_fold f xs (f i a)

/-- Scattering updates only the permutation workspace. -/
theorem scatter_eq (ref : Array Nat) (st : Search n) :
    scatter ref st = { st with workperm := ((List.range n).foldl
      (fun a i => a.set! ref[i]! st.lab[i]!) st.workperm) } := by
  rw [scatter]
  simp only [Id.run_bind, Id.run_pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hrange : List.range' [0:n].start [0:n].size [0:n].step = List.range n := by
    simp [List.range_eq_range']
  rw [hrange, forIn_fold]
  rfl

/-- Scattering preserves the allocated workspace size. -/
theorem scatter_size (ref : Array Nat) (st : Search n) :
    (scatter ref st).workperm.size = st.workperm.size := by
  rw [scatter_eq]
  exact foldl_scatter_size ref st.lab _ _

/-- Each reference vertex receives the corresponding current vertex. -/
theorem scatter_get {ref : Array Nat} {st : Search n}
    (hinj : ∀ i j, i < n → j < n → ref[i]! = ref[j]! → i = j)
    (hbound : ∀ i, i < n → ref[i]! < st.workperm.size)
    {i : Nat} (hi : i < n) :
    (scatter ref st).workperm[ref[i]!]! = st.lab[i]! := by
  rw [scatter_eq]
  exact foldl_scatter_getElem hinj hbound (Nat.le_refl _) hi

/-- A permutation reference assigns every position of the current labelling. -/
theorem scatter_map {ref : Array Nat} {st : Search n}
    (hwork : st.workperm.size = n)
    (href : ref.size = n) (hrefPerm : ref.toList.Perm (List.range n)) :
    ∀ i, i < n → (scatter ref st).workperm[ref[i]!]! = st.lab[i]! := by
  intro i hi
  apply scatter_get ?_ ?_ hi
  · intro a b ha hb heq
    have hn := hrefPerm.symm.nodup List.nodup_range
    apply (List.Nodup.getElem!_inj (by simpa [href] using ha)
      (by simpa [href] using hb) hn).mp
    have hla : ref.toList[a]! = ref[a]! := by
      rw [getElem!_pos ref a (by omega), getElem!_pos _ a (by simpa [href] using ha)]
      simp
    have hlb : ref.toList[b]! = ref[b]! := by
      rw [getElem!_pos ref b (by omega), getElem!_pos _ b (by simpa [href] using hb)]
      simp
    rw [hla, hlb]
    exact heq
  · intro j hj
    rw [hwork]
    apply List.mem_range.mp
    apply hrefPerm.mem_iff.mp
    rw [getElem!_pos ref j (by omega)]
    exact List.getElem_mem (by simpa [href] using hj)

/-- Equal leaf rows validate the scatter independently of its old contents. -/
theorem scatter_checked {ctx : Ctx n} {ref : Array Nat} {st : Search n}
    (hwork : st.workperm.size = n)
    (href : ref.size = n) (hrefPerm : ref.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx ref = leafRows ctx st.lab) :
    checkAutom ctx.g (scatter ref st).workperm = true :=
  checkAutom_scatter_of_leafRows_eq (by rw [scatter_size, hwork])
    href hrefPerm hlab hlabPerm (scatter_map hwork href hrefPerm) hrows

/-- A successful automorphism scan validates the reusable scatter. -/
theorem scatter_isautom {ctx : Ctx n} {ref : Array Nat} {st : Search n}
    (hwork : st.workperm.size = n)
    (href : ref.size = n) (hrefPerm : ref.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n))
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcheck : isautom ctx (scatter ref st).workperm = true) :
    checkAutom ctx.g (scatter ref st).workperm = true :=
  checkAutom_scatter_of_isautom (by rw [scatter_size, hwork])
    href hrefPerm hlab hlabPerm (scatter_map hwork href hrefPerm) hsymm hloop hcheck

end Hex.GraphIso.Nauty.Engine
