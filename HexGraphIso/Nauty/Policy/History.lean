/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Admission
public import HexGraphIso.Nauty.Invariant.Codes

public section

/-!
Target histories connect the first-code comparison to cheap admission.
Agreement of finite refinement codes only bounds the current depth by
the first leaf's depth. The recorded target positions, together with
the two descents from the cheap ancestor, supply the stronger geometric
fact needed by the scatter theorem.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Each individualization increases the descent level by one. -/
theorem DescPath.length {ctx : Ctx n} {base level : Nat}
    {root leaf : RefineSt n} {path : List (Nat × Nat)}
    (h : DescPath ctx base root path level leaf) :
    level = base + path.length := by
  induction h with
  | refl => simp
  | step tc e o hlvl hcell hne ho htail ih =>
    simp only [List.length_cons]
    omega

/-- Consecutive descents concatenate their individualization paths. -/
theorem DescPath.append {ctx : Ctx n} {base level last : Nat}
    {root middle leaf : RefineSt n} {xs ys : List (Nat × Nat)}
    (h₁ : DescPath ctx base root xs level middle)
    (h₂ : DescPath ctx level middle ys last leaf) :
    DescPath ctx base root (xs ++ ys) last leaf := by
  induction h₁ with
  | refl => exact h₂
  | step tc e o hlvl hcell hne ho htail ih =>
    exact .step tc e o hlvl hcell hne ho (ih h₂)

/-- Split a descent at a prescribed number of individualizations. -/
theorem DescPath.split {ctx : Ctx n} {base level : Nat}
    {root leaf : RefineSt n} {path : List (Nat × Nat)}
    (h : DescPath ctx base root path level leaf) {k : Nat}
    (hk : k ≤ path.length) :
    ∃ middle, DescPath ctx base root (path.take k) (base + k) middle ∧
      DescPath ctx (base + k) middle (path.drop k) level leaf := by
  induction h generalizing k with
  | refl base root =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨root, .refl _ _, .refl _ _⟩
  | @step base last root leaf path tc e o hlvl hcell hne ho htail ih =>
    cases k with
    | zero => exact ⟨root, .refl _ _, .step tc e o hlvl hcell hne ho htail⟩
    | succ k =>
      obtain ⟨middle, hpre, hpost⟩ := ih (k := k) (by simpa using hk)
      have hlevel : base + 1 + k = base + (k + 1) := by omega
      rw [hlevel] at hpre hpost
      exact ⟨middle, .step tc e o hlvl hcell hne ho hpre, hpost⟩

namespace Engine

/-- A list of target positions is stored at consecutive ancestor levels. -/
def Targets (store : Array Int) (base : Nat) (positions : List Nat) : Prop :=
  ∀ i, i < positions.length → store[base + i]! = Int.ofNat positions[i]!

/-- The initial segment of a stored target history reads the same slots. -/
theorem Targets.take {store : Array Int} {base : Nat} {xs : List Nat}
    (h : Targets store base xs) (k : Nat) : Targets store base (xs.take k) := by
  intro i hi
  have hix : i < xs.length := by
    have hlen := hi
    simp only [List.length_take] at hlen
    omega
  rw [getElem!_pos (xs.take k) i hi, List.getElem_take]
  simpa only [getElem!_pos xs i hix] using h i hix

/-- Two histories read from one store agree through the shorter history. -/
theorem Targets.prefix {store : Array Int} {base : Nat} {xs ys : List Nat}
    (hx : Targets store base xs) (hy : Targets store base ys)
    (hlen : xs.length ≤ ys.length) : xs <+: ys := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨hlen, ?_⟩
  intro i hi
  have heq := (hx i hi).symm.trans (hy i (Nat.lt_of_lt_of_le hi hlen))
  have hv : xs[i]! = ys[i]! := Int.ofNat_inj.mp heq
  simpa only [getElem!_pos xs i hi,
    getElem!_pos ys i (Nat.lt_of_lt_of_le hi hlen)] using hv

/-- Updating a later slot preserves an earlier target history. -/
theorem Targets.set_after {store : Array Int} {base slot : Nat} {xs : List Nat}
    (h : Targets store base xs) (hafter : base + xs.length ≤ slot) (value : Int) :
    Targets (store.set! slot value) base xs := by
  intro i hi
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
  exact h i hi

/-- A stored next target extends the history without changing the store. -/
theorem Targets.append {store : Array Int} {base : Nat} {xs : List Nat}
    (h : Targets store base xs) {tc : Nat}
    (htc : store[base + xs.length]! = Int.ofNat tc) :
    Targets store base (xs ++ [tc]) := by
  intro i hi
  by_cases heq : i = xs.length
  · subst i
    simpa using htc
  · have hilt : i < xs.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    rw [getElem!_append_left hilt]
    exact h i hilt

/-- Writing the next target extends its stored history. -/
theorem Targets.push {store : Array Int} {base : Nat} {xs : List Nat}
    (h : Targets store base xs) (hsize : base + xs.length < store.size) (tc : Nat) :
    Targets (store.set! (base + xs.length) (Int.ofNat tc)) base (xs ++ [tc]) := by
  intro i hi
  by_cases heq : i = xs.length
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hsize]
    simp
  · have hilt : i < xs.length := by
      simp only [List.length_append, List.length_singleton] at hi
      omega
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    rw [getElem!_append_left hilt]
    exact h i hilt

/-- A descent follows the target positions saved for the first path. -/
def Follows (ctx : Ctx n) (store : Array Int) (base : Nat) (root : RefineSt n)
    (level : Nat) (leaf : RefineSt n) : Prop :=
  ∃ path, DescPath ctx base root path level leaf ∧
    Targets store base (path.map Prod.fst)

/-- An empty descent follows any target store. -/
theorem Follows.refl (ctx : Ctx n) (store : Array Int) (base : Nat)
    (root : RefineSt n) : Follows ctx store base root base root :=
  ⟨[], .refl _ _, fun _ h => by simp at h⟩

/-- A later target update preserves a completed descent's history. -/
theorem Follows.set_after {ctx : Ctx n} {store : Array Int} {base level slot : Nat}
    {root leaf : RefineSt n} (h : Follows ctx store base root level leaf)
    (hafter : level ≤ slot) (value : Int) :
    Follows ctx (store.set! slot value) base root level leaf := by
  obtain ⟨path, hpath, htargets⟩ := h
  refine ⟨path, hpath, htargets.set_after ?_ value⟩
  simpa only [List.length_map, ← hpath.length] using hafter

/-- Individualizing a vertex in the stored target extends a descent. -/
theorem Follows.child {ctx : Ctx n} {store : Array Int} {base level tc e o : Nat}
    {root parent : RefineSt n} (h : Follows ctx store base root level parent)
    (hlevel : level < n) (hcell : (tc, e) ∈ cells parent.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc) (htc : store[level]! = Int.ofNat tc) :
    Follows ctx store base root (level + 1)
      (childSt ctx level parent tc parent.lab[tc + o]!) := by
  obtain ⟨path, hpath, htargets⟩ := h
  refine ⟨path ++ [(tc, o)], hpath.append
    (.step tc e o hlevel hcell hne ho (.refl _ _)), ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply htargets.append
  simpa only [List.length_map, ← hpath.length] using htc

/-- The first-code bound and stored descent histories justify cheap admission.
Equal leaf depths and rows follow from the small-cell subtree theorem. -/
theorem scatter_of_history {ctx : Ctx n} {st : Search n} {level : Nat}
    {cs fs : List Nat}
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (heq : st.eqlevFirst = level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {ancestor U V : RefineSt n}
    (hsmall : SubtreeOk ctx st.gcaFirst ancestor)
    (hU : Follows ctx st.firsttc st.gcaFirst ancestor fs.length U)
    (hV : Follows ctx st.firsttc st.gcaFirst ancestor level V)
    (hUd : ∀ i, i < n → U.ptn[i]! ≤ fs.length)
    (hVd : ∀ i, i < n → V.ptn[i]! ≤ level)
    (hfirst : st.firstlab = U.lab) (hcurrent : st.lab = V.lab)
    (hwork : st.workperm.size = n) :
    checkAutom ctx.g (scatter st.firstlab st).workperm = true := by
  obtain ⟨p₁, hU, ht₁⟩ := hU
  obtain ⟨p₂, hV, ht₂⟩ := hV
  apply scatter_of_descPaths hgsz hsymm hloop hsmall hU hV
    (ht₂.prefix ht₁ ?_) hUd hVd hfirst hcurrent hwork
  have hlen₁ := hU.length
  have hlen₂ := hV.length
  have hbound := hcodes.elev_fs
  simp only [List.length_map]
  omega

end Engine

end Hex.GraphIso.Nauty
