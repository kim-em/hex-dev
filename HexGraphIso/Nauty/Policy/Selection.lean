/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The refinement codes encountered along an individualization path, including its endpoint. -/
def pathCodes (ctx : Ctx n) : Nat → RefineSt n → List (Nat × Nat) → List Nat
  | _, st, [] => [st.longcode]
  | level, st, (tc, o) :: path =>
      st.longcode :: pathCodes ctx (level + 1) (childSt ctx level st tc st.lab[tc + o]!) path

/-- A descent has one refinement code at every node. -/
theorem pathCodes_length (ctx : Ctx n) (level : Nat) (st : RefineSt n) (path : List (Nat × Nat)) :
    (pathCodes ctx level st path).length = path.length + 1 := by
  induction path generalizing level st with
  | nil => rfl
  | cons a path ih =>
    cases a
    simp only [pathCodes, List.length_cons, ih]

/-- A consecutive segment of an array stores the codes of a path. -/
def StoredCodes (store : Array Nat) (base : Nat) (codes : List Nat) : Prop :=
  ∀ i, i < codes.length → store[base + i]! = codes[i]!

/-- A stored head and a stored suffix form a single code segment. -/
theorem StoredCodes.cons {store : Array Nat} {base code : Nat} {codes : List Nat}
    (head : store[base]! = code) (tail : StoredCodes store (base + 1) codes) :
    StoredCodes store base (code :: codes) := by
  intro i hi
  cases i with
  | zero => simpa using head
  | succ i =>
    simpa only [List.getElem!_cons_succ, show base + (i + 1) = base + 1 + i by omega]
      using tail i (by simpa using hi)

/-- A sentinel written after the path leaves every real code intact. -/
theorem StoredCodes.set_after {store : Array Nat} {base slot value : Nat} {codes : List Nat}
    (h : StoredCodes store base codes) (hafter : base + codes.length ≤ slot) :
    StoredCodes (store.set! slot value) base codes := by
  intro i hi
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
  exact h i hi

/-- Every target on a path is chosen by the unhinted specification rule. -/
def Selects (ctx : Ctx n) (tcLevel : Nat) :
    Nat → RefineSt n → List (Nat × Nat) → Prop
  | _, _, [] => True
  | level, st, (tc, o) :: path =>
    specTargetcell ctx st.lab st.ptn level tcLevel = tc ∧
      Selects ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + o]!) path

/-- Splitting a selected descent preserves the choices in its suffix. -/
theorem DescPath.split_selects {ctx : Ctx n} {tcLevel base level : Nat}
    {root leaf : RefineSt n} {path : List (Nat × Nat)}
    (h : DescPath ctx base root path level leaf)
    (hs : Selects ctx tcLevel base root path) {k : Nat}
    (hk : k ≤ path.length) :
    ∃ middle, DescPath ctx base root (path.take k) (base + k) middle ∧
      DescPath ctx (base + k) middle (path.drop k) level leaf ∧
      Selects ctx tcLevel (base + k) middle (path.drop k) := by
  induction h generalizing k with
  | refl base root =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact ⟨root, .refl _ _, .refl _ _, trivial⟩
  | @step base last root leaf path tc e o hlvl hcell hne ho htail ih =>
    cases k with
    | zero => exact ⟨root, .refl _ _, .step tc e o hlvl hcell hne ho htail, hs⟩
    | succ k =>
      obtain ⟨middle, hpre, hpost, hs⟩ := ih hs.2 (k := k) (by simpa using hk)
      have hlevel : base + 1 + k = base + (k + 1) := by omega
      rw [hlevel] at hpre hpost hs
      exact ⟨middle, .step tc e o hlvl hcell hne ho hpre, hpost, hs⟩

/-- Appending a newly selected target extends an unhinted path. -/
theorem Selects.append {ctx : Ctx n} {tcLevel base level tc o : Nat}
    {root leaf : RefineSt n} {path : List (Nat × Nat)}
    (h : DescPath ctx base root path level leaf)
    (hs : Selects ctx tcLevel base root path)
    (htc : specTargetcell ctx leaf.lab leaf.ptn level tcLevel = tc) :
    Selects ctx tcLevel base root (path ++ [(tc, o)]) := by
  induction h with
  | refl => exact ⟨htc, trivial⟩
  | step _ _ _ _ _ _ _ _ ih => exact ⟨hs.1, ih hs.2 htc⟩


/-- A suffix of the target history starts at the corresponding deeper level. -/
theorem Targets.drop {store : Array Int} {base : Nat} {xs : List Nat}
    (h : Targets store base xs) (k : Nat) :
    Targets store (base + k) (xs.drop k) := by
  intro i hi
  have hix : k + i < xs.length := by
    have hlen := hi
    simp only [List.length_drop] at hlen
    omega
  rw [getElem!_pos (xs.drop k) i hi, List.getElem_drop, Nat.add_assoc]
  simpa only [getElem!_pos xs (k + i) hix] using h (k + i) hix

/-- Histories of equal length read from the same store are equal. -/
theorem Targets.eq {store : Array Int} {base : Nat} {xs ys : List Nat}
    (hx : Targets store base xs) (hy : Targets store base ys)
    (hlen : xs.length = ys.length) : xs = ys :=
  List.IsPrefix.eq_of_length (hx.prefix hy (Nat.le_of_eq hlen)) hlen

/-- The first path's target choices determine the next unhinted target
of any non-discrete descent below a cheap ancestor that has followed
the stored targets so far. -/
theorem FollowsPerm.target {ctx : Ctx n} {store : Array Int}
    {tcLevel base level last : Nat} {root first current : RefineSt n}
    {path : List (Nat × Nat)}
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsmall : SubtreeOk ctx base root)
    (hfirst : DescPath ctx base root path last first)
    (hselected : Selects ctx tcLevel base root path)
    (hstored : Targets store base (path.map Prod.fst))
    (hcurrent : FollowsPerm ctx store base root level current)
    (hlevel : level ≤ last)
    (hdisc : ∀ i, i < n → first.ptn[i]! ≤ last)
    (hopen : ∃ i, i < n ∧ level < current.ptn[i]!) :
    Int.ofNat (specTargetcell ctx current.lab current.ptn level tcLevel) =
      store[level]! := by
  obtain ⟨V, ⟨p, hV, htV⟩, hperm⟩ := hcurrent
  have hlen := hV.length
  have hfirstlen := hfirst.length
  have hp : p.length ≤ path.length := by omega
  obtain ⟨middle, hpre, hpost, hsel⟩ := hfirst.split_selects hselected hp
  rw [← hlen] at hpre hpost hsel
  have htpre : Targets store base ((path.take p.length).map Prod.fst) := by
    rw [List.map_take]
    exact hstored.take p.length
  have htargets : p.map Prod.fst = (path.take p.length).map Prod.fst :=
    htV.eq htpre (by simp only [List.length_map, List.length_take, Nat.min_eq_left hp])
  have hptn : V.ptn = middle.ptn := descPath_ptn hgsz hsymm hloop
    hsmall hpre hV htargets
  have htc := descPath_target hgsz hsymm hloop hsmall hpre hV htargets tcLevel
  have hcurrenttc : specTargetcell ctx current.lab current.ptn level tcLevel =
      specTargetcell ctx V.lab V.ptn level tcLevel := by
    have hVok := descends_iterOk hV.descends hsmall.it
    have hpsz : current.ptn.size = n := by rw [← hperm.ptn, hVok.ok.ptnSize]
    have hend : current.ptn[current.ptn.size - 1]! ≤ level := by
      rw [← hperm.ptn]
      exact hVok.ok.ptnEnd
    have heq := specTargetcell_perm (ctx := ctx) (tcLevel := tcLevel)
      hperm.cells (Nat.le_of_eq hpsz.symm) hend
    rw [hperm.ptn]
    exact heq
  have htnext : Targets store level ((path.drop p.length).map Prod.fst) := by
    rw [List.map_drop]
    simpa only [← hlen] using hstored.drop p.length
  cases htail : path.drop p.length with
  | nil =>
    rw [htail] at hpost
    obtain ⟨rfl, rfl⟩ := descPath_nil hpost
    obtain ⟨i, hi, hlt⟩ := hopen
    have hle := hdisc i hi
    rw [← hptn, hperm.ptn] at hle
    omega
  | cons choice tail =>
    obtain ⟨tc, o⟩ := choice
    rw [htail] at hsel htnext
    have hread := htnext 0 (by simp)
    simp only [Nat.add_zero, List.map_cons, List.getElem!_cons_zero] at hread
    rw [hcurrenttc, htc, hsel.1]
    exact hread.symm


end Hex.GraphIso.Nauty
