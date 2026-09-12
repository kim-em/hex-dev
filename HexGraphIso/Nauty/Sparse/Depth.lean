/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstFields
public import HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Both refinement exits clean the actual accumulated code below the
terminal sentinel, regardless of input scratch or partition validity. -/
theorem refineWith_code_lt (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch) :
    (refineWith g level lab ptn active numcells scratch).longcode < codeSentinel := by
  rw [refineWith_parts]
  dsimp only
  split
  · change cleanup _ < codeSentinel
    rw [cleanup, codeSentinel]
    exact Nat.mod_lt _ (by omega)
  · split
    all_goals change cleanup _ < codeSentinel
    all_goals rw [cleanup, codeSentinel]
    all_goals exact Nat.mod_lt _ (by omega)

/-- A mismatching native target can only lower first-code agreement. -/
theorem chooseTarget_le (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget false g tcLevel level numcells st).2.2.2.eqlevFirst ≤ st.eqlevFirst := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.eqlevFirst ≤ st.eqlevFirst)
  mvcgen
  all_goals simp_all +zetaDelta
  all_goals omega

theorem classify_eqlev (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.eqlevFirst = st.eqlevFirst := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.eqlevFirst, ite_self]

/-- The real sparse off-path dispatch retains the terminal sentinel and
cannot extend first-code agreement below that saved leaf. -/
theorem depthPolicy (g : Graph n) (inf tcLevel last : Nat) :
    Generic.StablePolicy g inf tcLevel (Depth (n := n) (κ := Storage n) last)
      (fun code => code < codeSentinel) where
  code := fun level numcells st => refineWith_code_lt g level st.lab st.ptn st.active numcells st.canong.scratch
  visit := fun _ _ _ h => h
  compare := fun _ _ _ hc h => compareCodes_depth h hc
  target := by
    intro level numcells st h
    exact h.mono (chooseTarget_le g tcLevel level numcells st)
      ((referencePolicy g inf tcLevel).target level numcells st)
  classify := by
    intro level numcells st h
    exact ⟨h.mono (Nat.le_of_eq (classify_eqlev g level numcells st))
      (classify_reference g level numcells st), trivial⟩
  leaf := by
    intro leaf level st _ h
    exact h.mono (Nat.le_of_eq (leafExit_eqlev leaf level st)) (leafExit_reference leaf level st)
  cheap := by
    intro first level st h
    change Depth last (cheapCheck first level st)
    unfold cheapCheck
    split <;> exact h
  child := by
    intro first level tc tv st h
    cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    exact h.mono (recover_le inf level st) ((referencePolicy g inf tcLevel).recover level st)
  afterSweep := by
    intro level size index st h
    change Depth last (Nauty.afterSweep false level size index st)
    unfold Nauty.afterSweep
    split <;> exact h

theorem node_depth {g : Graph n} {inf tcLevel fuel level numcells last : Nat} {st : State n}
    (h : Depth last st) :
    Depth last (Generic.node false g inf tcLevel fuel level numcells st).2 :=
  Generic.node_stable (depthPolicy g inf tcLevel last) fuel level numcells st h

theorem sweep_depth {g : Graph n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index last : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : State n}
    (h : Depth last st) (hpast : Generic.Past first tv1 cursor) :
    Depth last (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 :=
  Generic.sweep_stable (depthPolicy g inf tcLevel last) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast h

/-- The actual first-path call retains its installed sentinel and depth
bound through every later branch of the production search. -/
theorem firstPath_depth {g : Graph n} {inf tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf)
    (hs : last + 1 < st.firstcode.size) :
    Depth last (Generic.node true g inf tcLevel fuel level numcells st).2 := by
  apply path.stable (depthPolicy g inf tcLevel last) (fun _ _ _ h => h) (by
    intro level size index st h
    change Depth last { (Nauty.afterSweep true level size index st) with
      order := (Nauty.afterSweep true level size index st).order * index }
    unfold Nauty.afterSweep
    split <;> exact h)
  change last ≤ last ∧ (leaf.firstcode.set! (last + 1) codeSentinel)[last + 1]! = codeSentinel
  refine ⟨Nat.le_refl _, Array.getElem!_set!_self _ _ _ ?_⟩
  have he := congrArg Prod.fst (firstPath_storeSize path)
  change leaf.firstcode.size = st.firstcode.size at he
  omega

end Hex.GraphIso.Nauty.Sparse
