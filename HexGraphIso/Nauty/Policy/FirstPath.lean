/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.First
public import HexGraphIso.Nauty.Policy.Leftmost
public import HexGraphIso.Nauty.Policy.Partition
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.Reach
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- Selecting a first-path target only writes its target slot and counter. -/
theorem chooseFirst_fields (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    let r := chooseTarget true ctx tcLevel level numcells st
    r.2.2.2 = { st with
      firsttc := st.firsttc.set! level r.1
      tctotal := r.2.2.2.tctotal } := by
  unfold chooseTarget
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
    Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, apply_ite Prod.snd]
  split <;> rfl

/-- A first-path preparation preserves the orbit array. -/
theorem prepareFirst_orbits (ctx : Ctx n) (tcLevel level numcells : Nat) (st : Search n) :
    (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.orbits = st.orbits := by
  unfold Generic.prepareFirst
  change (chooseTarget true ctx tcLevel level _ _).2.2.2.orbits = _
  rw [chooseFirst_fields]
  rfl

/-- A nontrivial first-path target contains a vertex. -/
theorem chooseFirst_nonempty {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) (hnc : numcells < n) :
    (chooseTarget true ctx tcLevel level numcells st).2.1 ≠ VSet.empty := by
  have hlive : bcount st.ptn level n < n := by
    have hc := hok.count
    change numcells = bcount st.ptn level n at hc
    omega
  obtain ⟨tc, len, hm, _, hlen, hrange⟩ := maketargetcell_open
    (ctx := ctx) (lab := st.lab) (ptn := st.ptn) (tcLevel := tcLevel) (hint := (-1 : Int))
    hlevel hok.ptnSize (searchOk_end hn0 hok hlevel) hlive
  have hne : (numcells != n) = true := bne_iff_ne.mpr (by omega)
  simp only [chooseTarget, hne, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    ite_true, ite_false, hm, Id.run_pure]
  refine mem_ne_empty (v := st.lab[tc]!) ?_
  rw [mem_worksetOf, Bool.and_eq_true]
  refine ⟨decide_eq_true (cellsReach_lt hok.reach tc (by omega)), ?_⟩
  rw [show tc + len - 1 + 1 - tc = len by omega]
  exact List.any_eq_true.mpr ⟨st.lab[tc]!,
    mem_segN_iff.mpr ⟨0, by omega, by rw [Nat.add_zero]⟩, by simp⟩

/-- Refining and selecting a first-path node preserves partition validity. -/
theorem prepareFirst_ok {G : Colored n k} {ctx : Ctx n}
    {tcLevel level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view) :
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    SearchOk G level r.1 r.2.2.2.2.view ∧
      Generic.Target Search.view level r.2.1.toNat r.2.2.1 r.2.2.2.2 := by
  let h := reachPolicy G ctx tcLevel hn0
  have hv := (h.visit level numcells st hlevel hok).1
  have hr := (h.record level (visit ctx level numcells st).2.1 _ _ hv).1
  have ht := h.target true level _ _ hlevel hr
  exact ⟨ht.1.1, ht.2⟩

/-- Every valid first-path state with identity orbits reaches a first leaf
within the same depth bound used by the executable engine. -/
theorem firstPath_exists {G : Colored n k} {ctx : Ctx n}
    {tcLevel fuel level numcells : Nat} {st : Search n}
    (hn0 : 0 < n) (hlevel : 1 ≤ level)
    (hok : SearchOk G level numcells st.view)
    (horbit : ∀ v, v < n → st.orbits[v]! = v)
    (hfuel : n + 1 ≤ level + fuel) :
    ∃ last leaf, Generic.FirstPath ctx tcLevel fuel level numcells st last leaf := by
  induction fuel generalizing level numcells st with
  | zero =>
    have := hok.bc
    have := bcount_le st.view.ptn level n
    omega
  | succ fuel ih =>
    let r := Generic.prepareFirst ctx tcLevel level numcells st
    obtain ⟨hr, ht⟩ := prepareFirst_ok (ctx := ctx) (tcLevel := tcLevel) hn0 hlevel hok
    by_cases hdisc : r.1 = n
    · exact ⟨level, r.2.2.2.2, .leaf fuel level numcells st hdisc⟩
    · have hnc : r.1 < n := by
        have hc : r.1 = bcount r.2.2.2.2.view.ptn level n := hr.count
        have hb := bcount_le r.2.2.2.2.view.ptn level n
        omega
      have hv := ((reachPolicy G ctx tcLevel hn0).visit level numcells st hlevel hok).1
      have hrec := ((reachPolicy G ctx tcLevel hn0).record level (visit ctx level numcells st).2.1 _ _ hv).1
      have hne : r.2.2.1 ≠ VSet.empty := chooseFirst_nonempty hn0 hlevel hrec hnc
      have htv := VSet.nextElem_none_eq_minElem hne
      let tv := r.2.2.1.minElem
      have hmem : r.2.2.1.mem tv = true := VSet.nextElem_mem htv
      let ready := cheapCheck true level r.2.2.2.2
      have hc := (reachPolicy G ctx tcLevel hn0).cheap true level r.1 r.2.2.2.2 hr
      have htarget : Generic.Target Search.view level r.2.1.toNat r.2.2.1 ready :=
        ht.of_out hc.2
      have hchild := ((reachPolicy G ctx tcLevel hn0).child true level r.1 r.2.1.toNat tv
        r.2.2.1 ready hlevel hc.1 htarget hmem).1
      have hoready : ready.orbits = st.orbits := by
        dsimp only [ready]
        unfold cheapCheck
        split <;> exact prepareFirst_orbits ctx tcLevel level numcells st
      have hochild : ∀ v, v < n →
          (child true level r.2.1.toNat tv ready).orbits[v]! = v := by
        intro v hv
        change ready.orbits[v]! = v
        rw [hoready]
        exact horbit v hv
      obtain ⟨last, leaf, hpath⟩ := ih (by omega) hchild hochild (by omega)
      refine ⟨last, leaf, .step hdisc htv ?_ hpath⟩
      change ready.orbits[tv]! = tv
      rw [hoready]
      exact horbit tv (VSet.mem_lt hmem)

/-- A valid first-path engine call returns the reference installed at its
actual first leaf; subsequent sibling search cannot replace it. -/
theorem firstPath_reference {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    (node true ctx inf tcLevel fuel level numcells st).2.reference =
      (firstterminal last leaf).reference := by
  rw [node_eq_generic]
  exact hpath.reference (referencePolicy ctx inf tcLevel) (fun _ _ _ => rfl)

/-- The nonempty initial state has a successful first descent at the root bound. -/
theorem initial_path (G : Colored n k) (hn0 : 0 < n) :
    ∃ last leaf, Generic.FirstPath { g := rowsOf G } 100 (n + 2) 1
      (initialPartition G).2.length
      (initial n (initialPartition G).1 (initialPartition G).2) last leaf := by
  apply firstPath_exists hn0 (Nat.le_refl _) (initial_ok G hn0)
  · intro v hv
    change (Array.ofFn (n := n) fun i : Fin n => i.val)[v]! = v
    rw [getElem!_pos _ _ (by simpa using hv), Array.getElem_ofFn]
  · omega

end Hex.GraphIso.Nauty.Engine
