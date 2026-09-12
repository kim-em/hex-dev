/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.LeafPath

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- A native selected reference descent retaining uniformity at and
below the saved all-same boundary. Every step is the literal cached child
operation, with its own bounded scratch and complete refinement code. -/
inductive RefPath (G : Hex.SparseGraph n) (tcLevel boundary : Nat) :
    Nat → RefineSt n → List Nat → Key n → Prop where
  | leaf {level : Nat} {st : RefineSt n} (label : Label n)
      (discrete : discreteAt st.ptn level n = true)
      (parse : Label.ofArray? n st.lab = some label) :
      RefPath G tcLevel boundary level st [] ⟨[st.longcode, codeSentinel], G.relabel label.perm⟩
  | step {level tc len o : Nat} {st : RefineSt n} {scratch : Scratch}
      {targets : List Nat} {key : Key n}
      (cell : IsCell st.ptn level tc len) (range : tc + len ≤ n)
      (nontrivial : 1 < len) (offset : o < len) (bounded : Scratch.Bounded n scratch)
      (target : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1))
      (child : RefPath G tcLevel boundary (level + 1)
        (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) targets key)
      (uniform : boundary ≤ level →
        Uniform G tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩) :
      RefPath G tcLevel boundary level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩

namespace RefPath

variable {G : Hex.SparseGraph n} {tcLevel boundary level : Nat} {st : RefineSt n}
  {targets : List Nat} {key : Key n}

/-- Forgetting boundary uniformity retains the literal selected descent. -/
theorem occurs (h : RefPath G tcLevel boundary level st targets key) :
    HasLeaf G tcLevel level st targets key := by
  induction h with
  | leaf label hd hp => exact HasLeaf.leaf hd hp
  | step hc hb hn ho hs ht _ _ ih => exact ih.step hc hb hn ho hs ht

theorem uniform (h : RefPath G tcLevel boundary level st targets key)
    (hr : RefineSt.Ready G level st) (hb : boundary ≤ level) :
    Uniform G tcLevel level st targets key := by
  cases h with
  | leaf label hd hp => exact Uniform.leaf hr hd hp
  | step _ _ _ _ _ _ _ hu => exact hu hb

/-- Moving the boundary deeper retains all required uniform subtrees. -/
theorem raise {boundary' : Nat} (h : RefPath G tcLevel boundary level st targets key)
    (hb : boundary ≤ boundary') : RefPath G tcLevel boundary' level st targets key := by
  induction h with
  | leaf label hd hp => exact .leaf label hd hp
  | step hc hr hn ho hs ht _ hu ih =>
    exact .step hc hr hn ho hs ht ih (fun hl => hu (Nat.le_trans hb hl))

end RefPath

/-- Every occurrence inside a uniform native subtree retains uniformity
along its whole actual path, at any chosen later boundary. -/
theorem HasLeaf.uniformPath {G : Hex.SparseGraph n} {tcLevel boundary level : Nat}
    {st : RefineSt n} {targets : List Nat} {key : Key n}
    (h : HasLeaf G tcLevel level st targets key) (hr : RefineSt.Ready G level st)
    (hu : Uniform G tcLevel level st targets key) :
    RefPath G tcLevel boundary level st targets key := by
  rcases h.cases with ⟨label, hd, hp, rfl, rfl⟩ |
    ⟨tc, len, o, scratch, rest, tail, hc, hb, hn, ho, hs, ht, hchild, rfl, rfl⟩
  · exact .leaf label hd hp
  · exact .step hc hb hn ho hs ht
      (hchild.uniformPath (hr.child hc hb hn ho scratch hs) (hu.child hc hb hn ho hs ht))
      (fun _ => hu)
termination_by targets.length

namespace RefPath

/-- Isomorphism transports the reference occurrence and every uniform
subtree retained at its boundary, preserving the full native key. -/
theorem map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel boundary level : Nat} {s t : RefineSt n} {targets : List Nat} {key : Key n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (he : RefineSt.Equiv (renamingOf p) level s t)
    (h : RefPath G tcLevel boundary level s targets key) :
    RefPath H tcLevel boundary level t targets key := by
  induction h generalizing t with
  | @leaf level s label hd hp =>
    have harray := he.discrete hs.spec.node.ptnSize
      (by simpa only [hs.spec.node.ptnSize] using hs.spec.node.ptnEnd)
      hs.spec.node.labSize ht.spec.node.labSize hd
    have hp' : Label.ofArray? n t.lab = some (⟨p.comp label.perm⟩ : Label n) := by
      rw [harray]
      exact SpecLeaf.parse_map p hs.spec.label hp
    have hg : H.relabel (p.comp label.perm) = G.relabel label.perm := by
      apply Hex.SparseGraph.ext
      intro i j
      simp only [Hex.SparseGraph.adj_relabel, Perm.get_comp]
      exact hiso _ _
    rw [he.code, ← hg]
    exact .leaf _ (by rw [he.ptn]; exact hd) hp'
  | @step level tc len o s scratch targets key hc hb hn ho hscratch htarget child hu ih =>
    let fresh := Scratch.fresh n
    have hfresh : Scratch.Bounded n fresh :=
      (Scratch.fresh_valid n t.lab t.ptn (level + 1)).toBounded
    obtain ⟨j, hj, _, hchild⟩ := child_match G H p hiso hs ht he.ptn he.count.symm he.cells
      hc hb hn ho scratch fresh hscratch hfresh
    have hc' : IsCell t.ptn level tc len := by rw [he.ptn]; exact hc
    have tail := ih (hs.child hc hb hn ho scratch hscratch) (ht.child hc' hb hn hj fresh hfresh) hchild
    have htarg := RefineSt.Equiv.target G H p hiso hs ht he tcLevel (-1)
    have hchoice : tc = targetcell (.ofGraph H) t.lab t.ptn level tcLevel (-1) :=
      htarget.trans htarg.symm
    rw [he.code]
    refine .step hc' hb hn hj hfresh hchoice tail ?_
    intro hboundary
    have hh := (hu hboundary).map G H p hiso hs ht he
    rwa [he.code] at hh

/-- Isomorphic native refined states have the same richer reference
occurrences, retaining all uniformity obligations in both directions. -/
theorem map_iff (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel boundary level : Nat} {s t : RefineSt n} {targets : List Nat} {key : Key n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (he : RefineSt.Equiv (renamingOf p) level s t) :
    RefPath G tcLevel boundary level s targets key ↔ RefPath H tcLevel boundary level t targets key := by
  constructor
  · exact RefPath.map G H p hiso hs ht he
  · have hback : ∀ i j, G.adj (p.inv.get i) (p.inv.get j) = H.adj i j := by
      intro i j
      simpa only [Perm.get_inv_get] using (hiso (p.inv.get i) (p.inv.get j)).symm
    have hc : cellsPerm s.ptn level s.lab (t.lab.map (renamingOf p.inv).toFun) := by
      apply cells_inverse hs.spec.node.labSize ht.spec.node.labSize hs.spec.node.ptnSize
        hs.spec.node.ptnEnd hs.spec.node.labOk he.cells
      intro v hv
      rw [renamingOf_lt p hv, renamingOf_lt p.inv (p.get ⟨v, hv⟩).isLt]
      exact congrArg Fin.val (Perm.inv_get_get p ⟨v, hv⟩)
    have hi : RefineSt.Equiv (renamingOf p.inv) level t s :=
      ⟨he.ptn.symm, by rw [he.ptn]; exact hc, he.control.symm, he.count.symm⟩
    exact RefPath.map H G p.inv hback ht hs hi

/-- An arbitrary checked cell stabilizer carries the richer reference
between literal cached children before any generation theorem is known. -/
theorem carried_iff {G : Hex.SparseGraph n} {tcLevel boundary level tc len a b : Nat}
    {st : RefineSt n} {scratch other : Scratch} {gamma : Array Nat}
    {targets : List Nat} {key : Key n}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len)
    (hs : Scratch.Bounded n scratch) (ht : Scratch.Bounded n other)
    (hcheck : checkAutom (Graph.context G).g gamma = true)
    (hstab : CellStab st.ptn level st.lab gamma)
    (hmove : gamma[st.lab[tc + a]!]! = st.lab[tc + b]!) :
    RefPath G tcLevel boundary (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + a]! scratch) targets key ↔
    RefPath G tcLevel boundary (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + b]! other) targets key := by
  obtain ⟨sigma, hval, hrows⟩ := checkAutom_sound (by simp [Graph.context]) hcheck
  have hiso := Graph.context_iso G G sigma hrows
  have he : cellsPerm st.ptn level st.lab (st.lab.map (renamingOf sigma.toPerm).toFun) := by
    rw [sigma.map_toPerm st.lab hr.spec.node.labOk]
    rw [map_congr_of_labOk hr.spec.node.labOk (fun v hv => hval v hv)]
    exact hstab
  have hv : st.lab[tc + a]! < n := perm_bound hr.spec.label (by omega)
  have hmove' : st.lab[tc + b]! = renamingOf sigma.toPerm st.lab[tc + a]! := by
    rw [renamingOf_lt sigma.toPerm hv, Renaming.get_toPerm, hval _ hv]
    exact hmove.symm
  obtain ⟨j, hj, hm, hchild⟩ := child_match G G sigma.toPerm hiso hr hr rfl rfl he
    hc hb hn ha scratch other hs ht
  have hjb : tc + j = tc + b := perm_injective hr.spec.label (by omega) (by omega)
    (hm.trans hmove'.symm)
  have heq : j = b := by omega
  subst j
  exact RefPath.map_iff G G sigma.toPerm hiso (hr.child hc hb hn ha scratch hs)
    (hr.child hc hb hn hb' other ht) hchild

/-- Forward transport through a checked cell stabilizer retains the
native reference and its saved uniformity boundary. -/
theorem carried {G : Hex.SparseGraph n} {tcLevel boundary level tc len a b : Nat}
    {st : RefineSt n} {scratch other : Scratch} {gamma : Array Nat}
    {targets : List Nat} {key : Key n}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len)
    (hs : Scratch.Bounded n scratch) (ht : Scratch.Bounded n other)
    (hcheck : checkAutom (Graph.context G).g gamma = true)
    (hstab : CellStab st.ptn level st.lab gamma)
    (hmove : gamma[st.lab[tc + a]!]! = st.lab[tc + b]!)
    (h : RefPath G tcLevel boundary (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + a]! scratch) targets key) :
    RefPath G tcLevel boundary (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + b]! other) targets key :=
  (carried_iff hr hc hb hn ha hb' hs ht hcheck hstab hmove).mp h

end RefPath

end Hex.GraphIso.Nauty.Sparse.Generation
