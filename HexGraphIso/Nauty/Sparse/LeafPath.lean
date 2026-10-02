/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeTransport
public import HexGraphIso.Nauty.Sparse.Key
public import HexGraphIso.Nauty.Sparse.Renaming
public import HexGraphIso.Nauty.Sparse.SubtreeMap
import all HexGraphIso.Nauty.Sparse.PathCodes

public section

namespace Hex.GraphIso.Nauty.Sparse.Generation

/-- A selected native descent ending in a parsed discrete leaf. The key
retains every executed refinement code and the terminal sentinel; every
child in its witness uses its own actual bounded scratch. -/
def HasLeaf (G : Hex.SparseGraph n) (tcLevel level : Nat) (root : RefineSt n)
    (targets : List Nat) (key : Key n) : Prop :=
  ∃ last leaf path codes, ∃ trace : CodePath G level root path last leaf codes,
    trace.Selects tcLevel ∧ discreteAt leaf.ptn last n = true ∧
    ∃ label, Label.ofArray? n leaf.lab = some label ∧
      targets = path.map Prod.fst ∧ key = ⟨codes ++ [codeSentinel], G.relabel label.perm⟩

namespace HasLeaf

variable {G : Hex.SparseGraph n} {tcLevel level : Nat} {st : RefineSt n}
  {targets : List Nat} {key : Key n}

theorem leaf {label : Label n} (hd : discreteAt st.ptn level n = true)
    (hp : Label.ofArray? n st.lab = some label) :
    HasLeaf G tcLevel level st [] ⟨[st.longcode, codeSentinel], G.relabel label.perm⟩ :=
  ⟨level, st, [], [st.longcode], .refl _ _, trivial, hd, label, hp, rfl, rfl⟩

/-- Prefixing the literal individualization and refinement preserves
the selected target and the complete native leaf key. -/
theorem step {tc len o : Nat} {scratch : Scratch}
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len)
    (hs : Scratch.Bounded n scratch)
    (ht : tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1))
    (h : HasLeaf G tcLevel (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) targets key) :
    HasLeaf G tcLevel level st (tc :: targets) ⟨st.longcode :: key.codes, key.graph⟩ := by
  obtain ⟨last, leaf, path, codes, trace, selected, hd, label, hp, rfl, rfl⟩ := h
  exact ⟨last, leaf, (tc, o) :: path, st.longcode :: codes,
    .step tc len o scratch hc hb hn ho hs trace, ⟨ht, selected⟩, hd, label, hp, rfl, rfl⟩

/-- Every valid native refined state has a selected discrete descendant.
The existing depth bound suffices while each chosen child uses fresh
bounded scratch as one permissible literal descent witness. -/
theorem nonempty (hr : RefineSt.Ready G level st) :
    ∃ targets key, HasLeaf G tcLevel level st targets key := by
  suffices ∀ fuel level st, RefineSt.Ready G level st → n < level + fuel →
      ∃ targets key, HasLeaf G tcLevel level st targets key by
    exact this (n + 1) level st hr (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro level st hr hf
    have hd := hr.spec.depth
    have hc := hr.spec.count
    have hb := bcount_le st.ptn level n
    omega
  | succ fuel ih =>
    intro level st hr hf
    by_cases hd : discreteAt st.ptn level n = true
    · obtain ⟨label, hp⟩ := Label.ofArray?_exists hr.spec.label
      exact ⟨[], _, HasLeaf.leaf hd hp⟩
    · have hc : bcount st.ptn level n < n := by
        have hb := bcount_le st.ptn level n
        have he : bcount st.ptn level n ≠ n := fun he =>
          hd ((discreteAt_iff_bcount hr.spec.node.ptnSize.symm hr.spec.node.ptnEnd).mpr he)
        omega
      let t := maketargetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1)
      obtain ⟨hcell, hn, hb⟩ := maketargetcell_valid G st.lab st.ptn level tcLevel (-1)
        hr.spec.label hr.spec.node.ptnSize
        (by simpa only [hr.spec.node.ptnSize] using hr.spec.node.ptnEnd) hc
      have hs : Scratch.Bounded n (Scratch.fresh n) :=
        (Scratch.fresh_valid n st.lab st.ptn (level + 1)).toBounded
      have ho : 0 < t.2.2 := by change 1 < t.2.2 at hn; omega
      obtain ⟨targets, key, hleaf⟩ := ih (level + 1)
        (st.child (.ofGraph G) level t.1 st.lab[t.1 + 0]! (Scratch.fresh n))
        (hr.child hcell hb hn ho _ hs) (by omega)
      exact ⟨t.1 :: targets, _, hleaf.step hcell hb hn ho hs rfl⟩

/-- A selected leaf occurrence is either the current discrete node or
an occurrence below one member of its actual unhinted target. -/
theorem cases (h : HasLeaf G tcLevel level st targets key) :
    (∃ label, discreteAt st.ptn level n = true ∧ Label.ofArray? n st.lab = some label ∧
      targets = [] ∧ key = ⟨[st.longcode, codeSentinel], G.relabel label.perm⟩) ∨
    (∃ tc len o scratch rest tail,
      IsCell st.ptn level tc len ∧ tc + len ≤ n ∧ 1 < len ∧ o < len ∧
      Scratch.Bounded n scratch ∧ tc = targetcell (.ofGraph G) st.lab st.ptn level tcLevel (-1) ∧
      HasLeaf G tcLevel (level + 1) (st.child (.ofGraph G) level tc st.lab[tc + o]! scratch) rest tail ∧
      targets = tc :: rest ∧ key = ⟨st.longcode :: tail.codes, tail.graph⟩) := by
  obtain ⟨last, leaf, path, codes, trace, selected, hd, label, hp, rfl, rfl⟩ := h
  cases trace with
  | refl => exact Or.inl ⟨label, hd, hp, rfl, rfl⟩
  | @step level last st leaf path codes tc len o scratch hc hb hn ho hs trace =>
    refine Or.inr ⟨tc, len, o, scratch, path.map Prod.fst,
      ⟨codes ++ [codeSentinel], G.relabel label.perm⟩,
      hc, hb, hn, ho, hs, selected.1, ?_, rfl, rfl⟩
    exact ⟨last, leaf, path, codes, trace, selected.2, hd, label, hp, rfl, rfl⟩

/-- Native descent transport preserves the complete leaf key under
isomorphism, including independently allocated scratch at every child. -/
theorem map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel level : Nat} {s t : RefineSt n} {targets : List Nat} {key : Key n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (he : RefineSt.Equiv (renamingOf p) level s t)
    (h : HasLeaf G tcLevel level s targets key) : HasLeaf H tcLevel level t targets key := by
  obtain ⟨last, leaf, path, codes, trace, selected, hd, label, hp, rfl, rfl⟩ := h
  obtain ⟨out, path', trace', selected', htcs, hend⟩ := trace.map G H p hiso hs ht he selected
  have hr := trace.descent.ready hs
  have hr' := trace'.descent.ready ht
  have harray := hend.discrete hr.spec.node.ptnSize
    (by simpa only [hr.spec.node.ptnSize] using hr.spec.node.ptnEnd)
    hr.spec.node.labSize hr'.spec.node.labSize hd
  have hp' : Label.ofArray? n out.lab = some (⟨p.comp label.perm⟩ : Label n) := by
    rw [harray]
    exact SpecLeaf.parse_map p hr.spec.label hp
  have hg : H.relabel (p.comp label.perm) = G.relabel label.perm := by
    apply Hex.SparseGraph.ext
    intro i j
    simp only [Hex.SparseGraph.adj_relabel, Perm.get_comp]
    exact hiso _ _
  refine ⟨last, out, path', codes, trace', selected', ?_, _, hp', htcs.symm, ?_⟩
  · rw [hend.ptn]; exact hd
  · rw [hg]

/-- Isomorphic native refined states have exactly the same selected
leaf keys and target sequences. The inverse transports every occurrence. -/
theorem map_iff (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {tcLevel level : Nat} {s t : RefineSt n} {targets : List Nat} {key : Key n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready H level t)
    (he : RefineSt.Equiv (renamingOf p) level s t) :
    HasLeaf G tcLevel level s targets key ↔ HasLeaf H tcLevel level t targets key := by
  constructor
  · exact HasLeaf.map G H p hiso hs ht he
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
    exact HasLeaf.map H G p.inv hback ht hs hi

/-- A checked cell stabilizer carrying one chosen vertex to another
transports every native leaf below those two literal cached children. -/
theorem carried {tc len a b : Nat} {scratch other : Scratch} {gamma : Array Nat}
    (hr : RefineSt.Ready G level st)
    (hc : IsCell st.ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len)
    (ha : a < len) (hb' : b < len)
    (hs : Scratch.Bounded n scratch) (ht : Scratch.Bounded n other)
    (hcheck : checkAutom (Graph.context G).g gamma = true)
    (hstab : CellStab st.ptn level st.lab gamma)
    (hmove : gamma[st.lab[tc + a]!]! = st.lab[tc + b]!)
    (h : HasLeaf G tcLevel (level + 1)
      (st.child (.ofGraph G) level tc st.lab[tc + a]! scratch) targets key) :
    HasLeaf G tcLevel (level + 1)
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
  exact h.map G G sigma.toPerm hiso (hr.child hc hb hn ha scratch hs)
    (hr.child hc hb hn hb' other ht) hchild

end HasLeaf
end Hex.GraphIso.Nauty.Sparse.Generation
