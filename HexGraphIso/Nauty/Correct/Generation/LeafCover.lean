/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Coverage
public import HexGraphIso.Nauty.Correct.Outcome

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- The reference occurrence sought in one frozen child of a sweep. -/
@[expose] def ChildLeaf (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (tc : Nat) (targets : List Nat) (key : Key n) (o : Nat) : Prop :=
  HasLeaf ctx tcLevel (level + 1) (childSt ctx level st tc st.lab[tc + o]!) targets key

/-- Coverage for an off-path sweep under the hypothesis that no visited
child produced the sought reference. Pruning may use any checked cell
stabilizer; membership in the final generated subgroup is not required. -/
structure LeafCover (ctx : Ctx n) (tcLevel level : Nat) (st : RefineSt n)
    (tc len : Nat) (targets : List Nat) (key : Key n) (tcell : VSet n)
    (cursor : Option Nat) : Prop where
  cover : ChildCover (ChildLeaf ctx tcLevel level st tc targets key)
    (fun o => st.lab[tc + o]!) (fun o => o < len)
    (fun o => ¬ ChildLeaf ctx tcLevel level st tc targets key o)
    (ChildLive st.lab tc len tcell cursor)
  past : ∀ o, o < len → tcell.mem st.lab[tc + o]! = true →
    ¬ After cursor st.lab[tc + o]! → ¬ ChildLeaf ctx tcLevel level st tc targets key o

namespace LeafCover

variable {ctx : Ctx n} {tcLevel level tc len : Nat} {st : RefineSt n}
    {targets : List Nat} {key : Key n} {tcell tcell' : VSet n} {cursor : Option Nat}

/-- Initially every occurrence is in the live target window. -/
theorem start (hlab : ∀ o, o < len → st.lab[tc + o]! < n) :
    LeafCover ctx tcLevel level st tc len targets key (windowSet n st.lab tc len) none := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl, Nat.le_refl _⟩
    exact mem_windowSet.mpr ⟨hlab o ho, mem_segN_iff.mpr ⟨o, ho, rfl⟩⟩
  · intro o _ _ h
    exact (h trivial).elim

/-- A child proved to have no matching occurrence advances the sweep. -/
theorem advance (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {tv : Nat} (hnext : tcell.nextElem cursor = some tv)
    (hcur : ∀ o, o < len → st.lab[tc + o]! = tv →
      ¬ ChildLeaf ctx tcLevel level st tc targets key o) :
    LeafCover ctx tcLevel level st tc len targets key tcell (some tv) := by
  constructor
  · apply ChildCover.step h.cover _ (fun _ hd => hd)
    intro o ho
    have hle := nextElem_le hnext ho.2.1 ho.2.2
    rcases Nat.eq_or_lt_of_le hle with he | hl
    · exact Or.inl (fun j hj => hj ▸ hcur o ho.1 he.symm)
    · exact Or.inr ⟨o, ⟨ho.1, ho.2.1, hl⟩, rfl, Nat.le_refl _⟩
  · intro o ho hm hpast
    rcases after_or_not cursor st.lab[tc + o]! with ha | ha
    · have hle := nextElem_le hnext hm ha
      exact hcur o ho (by change ¬ tv < st.lab[tc + o]! at hpast; omega)
    · exact h.past o ho hm ha

/-- A descending filter preserves absence coverage through arbitrarily
many earlier filters. Equality here is equality of occurrence propositions,
so it retains the target hints as well as the complete leaf key. -/
theorem filterDesc (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    (hstep : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = true ∨ ∃ j, j < len ∧
        ChildLeaf ctx tcLevel level st tc targets key o =
          ChildLeaf ctx tcLevel level st tc targets key j ∧ st.lab[tc + j]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    LeafCover ctx tcLevel level st tc len targets key tcell' cursor := by
  constructor
  · apply ChildCover.filterDesc h.cover
    · exact fun x y hxy hy => hxy ▸ hy
    · intro o ho
      rcases hstep o ho with hm | ⟨j, hj, he, hl⟩
      · exact Or.inl ⟨ho.1, hm, ho.2.2⟩
      · exact Or.inr ⟨j, hj, he, hl⟩
  · intro o ho hm ha
    exact h.past o ho (hsub _ hm) ha

/-- A checked cell stabilizer transports the entire reference occurrence
through a pruning step. It need not belong to the emitted generator list. -/
theorem filterAutom (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hdrop : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = false → ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab st.ptn level st.lab γ ∧ γ[st.lab[tc + o]!]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    LeafCover ctx tcLevel level st tc len targets key tcell' cursor := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  have hic : IsCell st.ptn level tc len := by
    rw [hlen]
    exact cells_isCell (by rw [hok.ok.ptnSize]; exact Nat.le_refl _) hok.ok.ptnEnd _ hcell
  apply h.filterDesc _ hsub
  intro o ho
  cases hm : tcell'.mem st.lab[tc + o]! with
  | true => exact Or.inl rfl
  | false =>
    obtain ⟨γ, hcheck, hstab, hlt⟩ := hdrop o ho hm
    have hW : (windowSet n st.lab tc len).mem γ[st.lab[tc + o]!]! = true :=
      windowSet_carry hstab hic (by rw [hok.ok.labSize]; omega) hok.ok.labOk
        (mem_windowSet.mpr ⟨hok.ok.labOk _ (by rw [hok.ok.labSize]; have := ho.1; omega),
          mem_segN_iff.mpr ⟨o, ho.1, rfl⟩⟩)
    obtain ⟨j, hj, hmap⟩ := mem_segN_iff.mp (mem_windowSet.mp hW).2
    refine Or.inr ⟨j, hj, ?_, ?_⟩
    · apply propext
      exact HasLeaf.carried_iff hok hlvl hgsz hcheck hstab hcell hne
        (by have := ho.1; omega) (by omega) hmap.symm
    · simpa only [hmap] using hlt

/-- The off-path long-prune ledger preserves every sought reference. -/
theorem longprune (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    {fixedpts : VSet n} {autos : Array (VSet n × VSet n)}
    (haut : ∀ p ∈ autos.toList, fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2) :
    LeafCover ctx tcLevel level st tc len targets key
      (Nauty.longprune tcell fixedpts autos) cursor := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  apply h.filterAutom hok hlvl hgsz hcell hne hlen
  · intro o ho hm
    exact longprune_drop (hok.ok.labOk _ (by rw [hok.ok.labSize]; have := ho.1; omega))
      ho.2.1 hm haut
  · exact fun _ hm => longprune_subset hm

/-- The off-path short-prune ledger preserves every sought reference,
including when the last pair is implicit. -/
theorem shortprune (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    {e : Nat} (hok : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc) {out : SearchSt n}
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g st.ptn st.lab level fix mcr) :
    LeafCover ctx tcLevel level st tc len targets key (Nauty.shortprune tcell out) cursor := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  apply h.filterAutom hok hlvl hgsz hcell hne hlen
  · intro o ho hm
    exact shortprune_drop (hok.ok.labOk _ (by rw [hok.ok.labSize]; have := ho.1; omega))
      ho.2.1 hm hlast
  · exact fun _ hm => shortprune_subset hm

/-- Exhausting a sweep with no matching visited child rules out every
matching child of the original target window. -/
theorem finish (h : LeafCover ctx tcLevel level st tc len targets key tcell cursor)
    (hnext : tcell.nextElem cursor = none) :
    ∀ o, o < len → ¬ ChildLeaf ctx tcLevel level st tc targets key o :=
  h.cover.finish (fun o ho => no_child_after hnext st.lab[tc + o]! ho.2.1 ho.2.2)

end LeafCover

end Hex.GraphIso.Nauty.Generation
