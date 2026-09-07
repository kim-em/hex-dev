/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Outcome

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- Every possible occurrence lies in a live child or has been ruled out.
The predicate is abstract so both ordinary leaves and references carrying
uniformity evidence use the same sweep coverage proof. -/
structure VisitCover (P : Nat → Prop) (lab : Array Nat)
    (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) : Prop where
  cover : ChildCover P
    (fun o => lab[tc + o]!) (fun o => o < len)
    (fun o => ¬ P o)
    (ChildLive lab tc len tcell cursor)
  past : ∀ o, o < len → tcell.mem lab[tc + o]! = true →
    ¬ After cursor lab[tc + o]! → ¬ P o

namespace VisitCover

variable {P : Nat → Prop} {lab : Array Nat} {tc len : Nat}
    {tcell tcell' : VSet n} {cursor : Option Nat}

/-- Initially every occurrence is in the live target window. -/
theorem start (hlab : ∀ o, o < len → lab[tc + o]! < n) :
    VisitCover P lab tc len (windowSet n lab tc len) none := by
  constructor
  · intro o ho
    refine Or.inr ⟨o, ⟨ho, ?_, trivial⟩, rfl, Nat.le_refl _⟩
    exact mem_windowSet.mpr ⟨hlab o ho, mem_segN_iff.mpr ⟨o, ho, rfl⟩⟩
  · intro o _ _ h
    exact (h trivial).elim

/-- A child proved to have no matching occurrence advances the sweep. -/
theorem advance (h : VisitCover P lab tc len tcell cursor)
    {tv : Nat} (hnext : tcell.nextElem cursor = some tv)
    (hcur : ∀ o, o < len → lab[tc + o]! = tv →
      ¬ P o) :
    VisitCover P lab tc len tcell (some tv) := by
  constructor
  · apply ChildCover.step h.cover _ (fun _ hd => hd)
    intro o ho
    have hle := nextElem_le hnext ho.2.1 ho.2.2
    rcases Nat.eq_or_lt_of_le hle with he | hl
    · exact Or.inl (fun j hj => hj ▸ hcur o ho.1 he.symm)
    · exact Or.inr ⟨o, ⟨ho.1, ho.2.1, hl⟩, rfl, Nat.le_refl _⟩
  · intro o ho hm hpast
    rcases after_or_not cursor lab[tc + o]! with ha | ha
    · have hle := nextElem_le hnext hm ha
      exact hcur o ho (by change ¬ tv < lab[tc + o]! at hpast; omega)
    · exact h.past o ho hm ha

/-- A descending filter preserves absence coverage through arbitrarily
many earlier filters. Equality here is equality of occurrence propositions,
so it retains the target hints as well as the complete leaf key. -/
theorem filterDesc (h : VisitCover P lab tc len tcell cursor)
    (hstep : ∀ o, ChildLive lab tc len tcell cursor o →
      tcell'.mem lab[tc + o]! = true ∨ ∃ j, j < len ∧
        P o =
          P j ∧ lab[tc + j]! < lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    VisitCover P lab tc len tcell' cursor := by
  constructor
  · apply ChildCover.filterDesc h.cover
    · exact fun x y hxy hy => hxy ▸ hy
    · intro o ho
      rcases hstep o ho with hm | ⟨j, hj, he, hl⟩
      · exact Or.inl ⟨ho.1, hm, ho.2.2⟩
      · exact Or.inr ⟨j, hj, he, hl⟩
  · intro o ho hm ha
    exact h.past o ho (hsub _ hm) ha

/-- An earlier original child has no occurrence, including when an
older filter removed it from the current target set. -/
theorem smaller (h : VisitCover P lab tc len tcell cursor)
    {tv o : Nat} (hnext : tcell.nextElem cursor = some tv)
    (ho : o < len) (hlt : lab[tc + o]! < tv) : ¬ P o := by
  rcases h.cover o ho with hd | ⟨j, hj, _, hle⟩
  · exact hd
  · have hmin := nextElem_le hnext hj.2.1 hj.2.2
    dsimp only at hle
    omega

/-- A checked carrier transfers absence from a reference child to the
current child. The carrier belongs to the frozen cell stabilizer. -/
theorem carrier {ctx : Ctx n} {level : Nat} {ptn : Array Nat}
    (h : VisitCover P lab tc len tcell cursor)
    {tv oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv) (hpos : tc < n)
    (href : oRef < len) (habsent : ¬ P oRef)
    (hcarrier : CellCarrier ctx ptn level lab ref cur store)
    (hatRef : ref[tc]! = lab[tc + oRef]!) (hatCur : cur[tc]! = tv)
    (hcarry : ∀ {γ o j}, checkAutom ctx.g γ = true → CellStab ptn level lab γ →
      o < len → j < len → γ[lab[tc + o]!]! = lab[tc + j]! → (P o ↔ P j)) :
    VisitCover P lab tc len tcell (some tv) := by
  obtain ⟨γ, _, hcheck, hmap, hstab⟩ := hcarrier
  apply h.advance hnext
  intro o ho hat
  have hact : γ[lab[tc + oRef]!]! = lab[tc + o]! := by
    rw [← hatRef, hat, ← hatCur]
    exact hmap tc hpos
  exact fun hleaf => habsent ((hcarry hcheck hstab href ho hact).mpr hleaf)

/-- A carrier to an earlier reference discharges the current child using
the ranked coverage invariant, without claiming exhaustive search. -/
theorem reference {ctx : Ctx n} {level : Nat} {ptn : Array Nat}
    (h : VisitCover P lab tc len tcell cursor)
    {tv oRef : Nat} {ref cur : Array Nat} {store : Array (Array Nat)}
    (hnext : tcell.nextElem cursor = some tv) (hpos : tc < n)
    (href : oRef < len) (hearlier : lab[tc + oRef]! < tv)
    (hcarrier : CellCarrier ctx ptn level lab ref cur store)
    (hatRef : ref[tc]! = lab[tc + oRef]!) (hatCur : cur[tc]! = tv)
    (hcarry : ∀ {γ o j}, checkAutom ctx.g γ = true → CellStab ptn level lab γ →
      o < len → j < len → γ[lab[tc + o]!]! = lab[tc + j]! → (P o ↔ P j)) :
    VisitCover P lab tc len tcell (some tv) :=
  h.carrier hnext hpos href (h.smaller hnext href hearlier) hcarrier hatRef hatCur hcarry

/-- A checked cell stabilizer transports the entire reference occurrence
through a pruning step. It need not belong to the emitted generator list. -/
theorem filterAutom {ctx : Ctx n} {level : Nat} {st : RefineSt n} (h : VisitCover P st.lab tc len tcell cursor)
    {e : Nat} (hok : IterOk ctx level st)
    (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hcarry : ∀ {γ o j}, checkAutom ctx.g γ = true → CellStab st.ptn level st.lab γ →
      o < len → j < len → γ[st.lab[tc + o]!]! = st.lab[tc + j]! → (P o ↔ P j))
    (hdrop : ∀ o, ChildLive st.lab tc len tcell cursor o →
      tcell'.mem st.lab[tc + o]! = false → ∃ γ, checkAutom ctx.g γ = true ∧
        CellStab st.ptn level st.lab γ ∧ γ[st.lab[tc + o]!]! < st.lab[tc + o]!)
    (hsub : ∀ v, tcell'.mem v = true → tcell.mem v = true) :
    VisitCover P st.lab tc len tcell' cursor := by
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
      exact hcarry hcheck hstab ho.1 hj hmap.symm
    · simpa only [hmap] using hlt

/-- The off-path long-prune ledger preserves every sought reference. -/
theorem longprune {ctx : Ctx n} {level : Nat} {st : RefineSt n} (h : VisitCover P st.lab tc len tcell cursor)
    {e : Nat} (hok : IterOk ctx level st)
    (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hcarry : ∀ {γ o j}, checkAutom ctx.g γ = true → CellStab st.ptn level st.lab γ →
      o < len → j < len → γ[st.lab[tc + o]!]! = st.lab[tc + j]! → (P o ↔ P j))
    {fixedpts : VSet n} {autos : Array (VSet n × VSet n)}
    (haut : ∀ p ∈ autos.toList, fixedpts.subset p.1 = true →
      PairOk ctx.g st.ptn st.lab level p.1 p.2) :
    VisitCover P st.lab tc len
      (Nauty.longprune tcell fixedpts autos) cursor := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  apply h.filterAutom hok hcell hne hlen hcarry
  · intro o ho hm
    exact longprune_drop (hok.ok.labOk _ (by rw [hok.ok.labSize]; have := ho.1; omega))
      ho.2.1 hm haut
  · exact fun _ hm => longprune_subset hm

/-- The off-path short-prune ledger preserves every sought reference,
including when the last pair is implicit. -/
theorem shortprune {ctx : Ctx n} {level : Nat} {st : RefineSt n} (h : VisitCover P st.lab tc len tcell cursor)
    {e : Nat} (hok : IterOk ctx level st)
    (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hlen : len = e + 1 - tc)
    (hcarry : ∀ {γ o j}, checkAutom ctx.g γ = true → CellStab st.ptn level st.lab γ →
      o < len → j < len → γ[st.lab[tc + o]!]! = st.lab[tc + j]! → (P o ↔ P j)) {out : SearchSt n}
    (hlast : ∀ fix mcr, out.autos.back? = some (fix, mcr) →
      PairOk ctx.g st.ptn st.lab level fix mcr) :
    VisitCover P st.lab tc len (Nauty.shortprune tcell out) cursor := by
  have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
  apply h.filterAutom hok hcell hne hlen hcarry
  · intro o ho hm
    exact shortprune_drop (hok.ok.labOk _ (by rw [hok.ok.labSize]; have := ho.1; omega))
      ho.2.1 hm hlast
  · exact fun _ hm => shortprune_subset hm

/-- Exhausting a sweep with no matching visited child rules out every
matching child of the original target window. -/
theorem finish (h : VisitCover P lab tc len tcell cursor)
    (hnext : tcell.nextElem cursor = none) :
    ∀ o, o < len → ¬ P o :=
  h.cover.finish (fun o ho => no_child_after hnext lab[tc + o]! ho.2.1 ho.2.2)


end VisitCover

end Hex.GraphIso.Nauty.Generation
