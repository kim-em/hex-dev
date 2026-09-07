/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.History
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The stored first-reference codes and target hints before a level agree. -/
@[expose] def PrefixEq (level : Nat) (st out : SearchSt n) : Prop :=
  ∀ i, i < level → out.firstcode[i]! = st.firstcode[i]! ∧ out.firsttc[i]! = st.firsttc[i]!

namespace PrefixEq

theorem refl (level : Nat) (st : SearchSt n) : PrefixEq level st st := fun _ _ => ⟨rfl, rfl⟩

theorem trans {level : Nat} {a b c : SearchSt n}
    (h : PrefixEq level a b) (h' : PrefixEq level b c) : PrefixEq level a c :=
  fun i hi => ⟨(h' i hi).1.trans (h i hi).1, (h' i hi).2.trans (h i hi).2⟩

theorem mono {level level' : Nat} {st out : SearchSt n}
    (h : PrefixEq level st out) (hle : level' ≤ level) : PrefixEq level' st out :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hle)

end PrefixEq

theorem FirstFields.prefix {st out : SearchSt n} (h : FirstFields st out) (level : Nat) :
    PrefixEq level st out := by
  intro i _
  rw [h.codes, h.targets]
  exact ⟨rfl, rfl⟩

private theorem firstLoop_prefix {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n),
      PrefixEq level st (firstPathNode ctx inf tcLevel fuel level numcells st).2) :
    ∀ cfuel level numcells tc tv1 cursor tcell index (st : SearchSt n),
      PrefixEq level st (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
        cursor tcell index st).2.2 := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell index st
    simpa only [firstChildLoop] using PrefixEq.refl level st
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell index st
    cases cursor with
    | none => simpa only [firstChildLoop] using PrefixEq.refl level st
    | some tv =>
      cases hrep : st.orbits[tv]! == tv with
      | false =>
        rw [firstChildLoop_skip ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st hrep]
        exact ih _ _ _ _ _ _ _ _
      | true =>
        let child : SearchSt n := { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        cases hfirst : tv == tv1 with
        | false =>
          have hc := (other_fields ctx inf tcLevel fuel (level + 1) (numcells + 1) child).prefix level
          obtain ⟨r, out, hout⟩ : ∃ r out,
              otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
          rw [hout] at hc
          by_cases hearly : r < Int.ofNat level
          · rw [firstChildLoop_earlyOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
              r out hrep hfirst hout hearly]
            exact hc
          · rw [firstChildLoop_stayOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
              r out hrep hfirst hout hearly]
            dsimp only
            apply PrefixEq.trans _ (ih _ _ _ _ _ _ _ _)
            apply hc.trans
            apply PrefixEq.trans _ ((FirstFields.recover inf level _).prefix level)
            cases out.needshortprune <;> intro i hi <;> exact ⟨rfl, rfl⟩
        | true =>
          have hc := (hnode (level + 1) (numcells + 1) child).mono (Nat.le_succ level)
          obtain ⟨r, out, hout⟩ : ∃ r out,
              firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
          rw [hout] at hc
          by_cases hearly : r < Int.ofNat level
          · rw [firstChildLoop_earlyGuide ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
              r out hrep hfirst hout hearly]
            exact hc
          · rw [firstChildLoop_stayGuide ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
              r out hrep hfirst hout hearly]
            dsimp only
            apply PrefixEq.trans _ (ih _ _ _ _ _ _ _ _)
            apply hc.trans
            apply PrefixEq.trans _ ((FirstFields.recover inf level _).prefix level)
            cases out.needshortprune <;> intro i hi <;> exact ⟨rfl, rfl⟩

/-- First-path recursion writes reference codes and target hints only at
its own level and below. This is unconditional, including fuel exhaustion. -/
theorem first_prefix (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ fuel level numcells (st : SearchSt n),
      PrefixEq level st (firstPathNode ctx inf tcLevel fuel level numcells st).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st
    simpa only [firstPathNode] using PrefixEq.refl level st
  | succ fuel ih =>
    intro level numcells st
    by_cases hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n
    · rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
      intro i hi
      constructor
      · rw [ftF_firstcode, Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact Array.getElem!_set!_ne _ _ _ _ (by omega)
      · rw [firstterminal]
        simp only [Id.run_bind, Id.run_pure]
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact Array.getElem!_set!_ne _ _ _ _ (by omega)
    · let rs := refine ctx level st.lab st.ptn st.active numcells
      let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      let pre0 : SearchSt n := { st with
        lab := rs.lab, ptn := rs.ptn, active := rs.active,
        firstcode := st.firstcode.set! level rs.longcode,
        firsttc := st.firsttc.set! level (Int.ofNat mt.1),
        numnodes := st.numnodes + 1, tctotal := st.tctotal + mt.2.2 }
      let pre := if pre0.noncheaplevel ≥ level ∧ ¬ cheapautom pre0.ptn level n then
        { pre0 with noncheaplevel := level + 1 } else pre0
      have hpre : PrefixEq level st pre := by
        intro i hi
        dsimp only [pre]
        split <;> constructor <;> exact Array.getElem!_set!_ne _ _ _ _ (by omega)
      have hl := hpre.trans (firstLoop_prefix ih (n + 1) level rs.numcells mt.1
        ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre)
      rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
      change PrefixEq level st (match (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
          mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).1 with
        | some r => (r, (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
            mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.2)
        | none => (Int.ofNat level - 1, firstFinish level mt.2.2
            (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
              ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.1
            (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
              ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.2)).2
      generalize he : firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
        ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre = result at hl ⊢
      obtain ⟨r, index, out⟩ := result
      cases r with
      | some r => exact hl
      | none =>
        dsimp only
        unfold firstFinish
        split <;> exact hl

end Hex.GraphIso.Nauty.Generation
