/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.First.Return
import all HexGraphIso.Nauty.Policy.First.Return
import all HexGraphIso.Nauty.Policy.Colors
import all HexGraphIso.Nauty.Policy.First.Entry
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Safety
import all HexGraphIso.Nauty.Policy.Invariant
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- A sweep's first child establishes the state used by every later off-path sibling. -/
theorem firstSweep_safe {G : Colored n k} {ctx : Ctx n} {tcLevel fuel cfuel : Nat}
    (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (level numcells tc tv index : Nat) (cell : VSet n) (st : Search n)
    (horbit : st.orbits[tv]! = tv)
    (hchild : RunInv G ctx (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
      (child true level tc tv st)).2)
    (hready : let out := (node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
        (child true level tc tv st)).2
      let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
      SweepPre G ctx tcLevel true level numcells tc tv none cell
        (Nauty.recover (n + 2) level left)) :
    RunInv G ctx (sweep true ctx (n + 2) tcLevel fuel (cfuel + 1)
      level numcells tc tv (some tv) cell index st).2.2 := by
  dsimp only at hready
  rw [sweep]
  simp only [Bool.not_true, horbit, beq_self_eq_true, Bool.or_true,
    Bool.and_self, Bool.false_and, ite_true]
  generalize hcall : node true ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
    (child true level tc tv st) = result at hchild hready ⊢
  obtain ⟨exit, out⟩ := result
  let left := { afterChildFirst level tv out with fixedpts := out.fixedpts.erase tv }
  let ready := Nauty.recover (n + 2) level left
  have hleft : RunInv G ctx left := hchild.congr (out := left) rfl rfl hchild.cache rfl rfl rfl rfl rfl
  have hcontinue : ∀ smaller index, (∀ v, smaller.mem v = true → cell.mem v = true) →
      RunInv G ctx (sweep true ctx (n + 2) tcLevel fuel cfuel level numcells tc tv
        (smaller.nextElem (some tv)) smaller index ready).2.2 := by
    intro smaller index hsub
    apply sweep_safe hn0 hgsz hsymm hloop
    refine ⟨?_, hready.positive, hready.partition, hready.target.subset hsub,
      (fun _ hv => VSet.nextElem_mem hv), hready.stored, hready.ancestor, hready.canonAncestor, hready.history, hready.recorded, hready.equitable, hready.boundary, hready.cheapBound, hready.path, hready.small⟩
    intro _ v hv
    have hn := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hn
    omega
  cases exit with
  | fuel => exact hleft
  | done => exact hcontinue cell _ (fun _ hv => hv)
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hleft
    · cases short with
      | false => exact hcontinue cell _ (fun _ hv => hv)
      | true =>
        exact hcontinue (shortprune cell left) _
          (fun _ hv => Nauty.shortprune_subset (st := left) hv)

/-- A first-path node consists of its prepared partition and the sweep of its chosen target. -/
theorem node_first (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n) :
    node true ctx inf tcLevel (fuel + 1) level numcells st = Id.run (do
      let r := Generic.prepareFirst ctx tcLevel level numcells st
      if r.1 == n then return (.unwind (level - 1) false, firstterminal level r.2.2.2.2)
      let s := sweep true ctx inf tcLevel fuel (n + 1) level r.1 r.2.1.toNat
        ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (cheapCheck true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false, afterSweep true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)) := by
  rw [node]
  rfl

/-- Installing the first leaf establishes the persistent invariant. -/
theorem FirstPre.firstterminal {G : Colored n k} {ctx : Ctx n} {level numcells : Nat}
    {st : Search n} (h : FirstPre G ctx level numcells st) (hn0 : 0 < n) (tcLevel : Nat) :
    RunInv G ctx (Nauty.firstterminal level (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2) := by
  have hp := (prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 h.positive h.partition).1
  have hs := prepareFirst_stores ctx tcLevel level numcells st
  refine ⟨isPerm_of_cellsReach hp.labSize hn0 hp.reach, ⟨hp.labSize, hp.reach⟩, ?_,
    hs.2.2.2.1.trans h.scratch, ?_, ?_, hp.reach, h.colors.congr hs.2.2.2.2,
    h.pairs.congr (prepareFirst_autos ctx tcLevel level numcells st),
    h.workspace.ofFields (prepareFirst_capacity ctx tcLevel level numcells st)
      (prepareFirst_autos ctx tcLevel level numcells st)⟩
  · apply canongInv_zero
    change (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.canong.size = n
    rw [hs.2.2.1, h.cache]
  · intro γ hγ
    change γ ∈ (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.genTrace at hγ
    rw [hs.2.2.2.2] at hγ
    exact h.trace γ hγ
  · exact h.orbits.congr hs.2.2.2.2 (prepareFirst_orbits ctx tcLevel level numcells st)

/-- The first descent establishes the off-path invariant before any later sibling can be searched. -/
theorem firstPath_safe {G : Colored n k} {ctx : Ctx n} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (hn0 : 0 < n) (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hin : FirstPre G ctx level numcells st) :
    RunInv G ctx (node true ctx (n + 2) tcLevel fuel level numcells st).2 := by
  induction hpath with
  | leaf fuel level numcells st hdisc =>
    rw [node_first]
    simp only [hdisc, beq_self_eq_true, ite_true, Id.run_pure]
    exact hin.firstterminal hn0 tcLevel
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    let ready := cheapCheck true level r.2.2.2.2
    have hchild := ih (hin.child hn0 hsymm htv hgsz hloop)
    have hready := firstChild_ready hin hn0 hsymm hopen htv horbit tail hchild hgsz hloop
    have hs := firstSweep_safe (cfuel := n) hn0 hgsz hsymm hloop level r.1 r.2.1.toNat tv 0
      r.2.2.1 ready horbit hchild hready
    rw [node_first]
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false, htv, Option.getD_some]
    generalize hsval : sweep true ctx (n + 2) tcLevel fuel (n + 1) level r.1 r.2.1.toNat
      tv (some tv) r.2.2.1 0 ready = result at hs ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact hs
    | unwind => exact hs
    | done => exact hs.afterSweep true level r.2.2.2.1 index

/-- The coloured initial state satisfies the first-descent entry conditions. -/
theorem initial_firstPre (G : Colored n k) (hn0 : 0 < n) :
    FirstPre G { g := rowsOf G } 1 (initialPartition G).2.length
      (initial n (initialPartition G).1 (initialPartition G).2) := by
  refine ⟨Nat.le_refl _, initial_ok G hn0, initial_equitable G hn0,
    Array.size_replicate, ?_, Array.size_replicate, Array.size_replicate, ?_,
    initial_orbits n (initialPartition G).1 (initialPartition G).2, ?_, ?_,
    initial_boundary G hn0 { g := rowsOf G }, Nat.le_refl _, initial_pairs G { g := rowsOf G }, by change 0 < 500 ∧ 0 ≤ 500; decide,
    initial_pathInv G { g := rowsOf G }, (initial_nodeOk G hn0).starts⟩
  · change n < (Array.replicate (n + 2) (-1 : Int)).size
    rw [Array.size_replicate]
    omega
  · intro γ hγ
    change γ ∈ (#[] : Array (Array Nat)) at hγ
    simp at hγ
  · intro γ hγ
    change γ ∈ (#[] : Array (Array Nat)) at hγ
    simp at hγ
  · intro hsmall
    change 1 < 1 at hsmall
    omega

/-- Every nonempty engine run installs valid leaf data and only checked generators. -/
theorem runState_safe (G : Colored n k) (hn0 : 0 < n) :
    RunInv G { g := rowsOf G }
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  obtain ⟨last, leaf, hpath⟩ := initial_path G hn0
  rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn0)]
  exact firstPath_safe hn0 (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
    hpath (initial_firstPre G hn0)

/-- The complete engine's generator trace is valid, including the empty graph. -/
theorem runState_checked (G : Colored n k) :
    TraceOk { g := rowsOf G }
      (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2 := by
  by_cases hn0 : n = 0
  · subst n
    intro γ hγ
    change γ ∈ (#[] : Array (Array Nat)) at hγ
    simp at hγ
  · exact (runState_safe G (by omega)).trace

/-- Every automorphism reported by the structured engine passes the certificate check. -/
theorem runColoredTraced_checked (G : Colored n k) {γ : Array Nat}
    (hγ : γ ∈ (runColoredTraced G).autos) : checkAutom (rowsOf G) γ = true :=
  runState_checked G γ hγ

end Hex.GraphIso.Nauty
