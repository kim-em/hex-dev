/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Transitive

public section

/-!
A discrete descent through a prefix of another descent's target
positions cannot stop earlier below a cheap ancestor. Individualizing
corresponding vertices transports the remaining first descent to the
current child. If the current descent ends, its discrete partition
cannot contain the nontrivial target cell needed to continue the other.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- A row-preserving renaming and a reordering inside cells leave the
next target position unchanged. -/
theorem stPerm_target {σ : Renaming n} {level tcLevel : Nat}
    {U V : RefineSt n} (hg : RowsMap σ ctx.g ctx.g)
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U)) :
    specTargetcell ctx V.lab V.ptn level tcLevel =
      specTargetcell ctx U.lab U.ptn level tcLevel := by
  have hV := iterOk_of_stPerm hU hsp
  calc
    specTargetcell ctx V.lab V.ptn level tcLevel =
        specTargetcell ctx (U.lab.map σ.toFun) V.ptn level tcLevel :=
      specTargetcell_perm hsp.cells (Nat.le_of_eq hV.ok.ptnSize.symm) hV.ok.ptnEnd
    _ = specTargetcell ctx U.lab U.ptn level tcLevel := by
      rw [← hsp.ptn]
      exact specTargetcell_map σ hg hU.ok.labOk hU.ok.labSize
        hU.ok.ptnSize hU.ok.ptnEnd

/-- Descents following the same target positions below a cheap ancestor
agree on every quantity invariant under cell reordering and automorphisms. -/
theorem descPath_invariant {α : Type} (f : Nat → RefineSt n → α)
    (hf : ∀ {σ : Renaming n} {level : Nat} {U V : RefineSt n},
      RowsMap σ ctx.g ctx.g → IterOk ctx level U →
      StPerm level V (mapSt σ U) → f level V = f level U)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (tcs : List Nat) :
    ∀ {level : Nat} {st : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
      {last : Nat} {U V : RefineSt n},
      SubtreeOk ctx level st →
      DescPath ctx level st p₁ last U → p₁.map Prod.fst = tcs →
      DescPath ctx level st p₂ last V → p₂.map Prod.fst = tcs →
      f last V = f last U := by
  induction tcs with
  | nil =>
    intro level st p₁ p₂ last U V hS hU hp₁ hV hp₂
    have h1 : p₁ = [] := by simpa using hp₁
    have h2 : p₂ = [] := by simpa using hp₂
    subst h1
    subst h2
    obtain ⟨_, rfl⟩ := descPath_nil hU
    obtain ⟨_, rfl⟩ := descPath_nil hV
    rfl
  | cons tc tcs ih =>
    intro level st p₁ p₂ last U V hS hU hp₁ hV hp₂
    cases p₁ with
    | nil => simp at hp₁
    | cons a₁ tl₁ =>
    cases p₂ with
    | nil => simp at hp₂
    | cons a₂ tl₂ =>
    obtain ⟨tc₁, o₁⟩ := a₁
    obtain ⟨tc₂, o₂⟩ := a₂
    simp only [List.map_cons, List.cons.injEq] at hp₁ hp₂
    obtain ⟨htc₁, ht₁⟩ := hp₁
    obtain ⟨htc₂, ht₂⟩ := hp₂
    subst tc₁
    subst tc₂
    cases hU with
    | step _ e₁ _ hlvl hcell₁ hne₁ ho₁ htail₁ =>
    cases hV with
    | step _ e₂ _ _ hcell₂ _ ho₂ htail₂ =>
    have hee : e₁ = e₂ := cells_eq_of_start
      (Nat.le_of_eq hS.it.ok.ptnSize.symm) hS.it.ok.ptnEnd hcell₁ hcell₂
    subst hee
    by_cases hval : st.lab[tc + o₁]! = st.lab[tc + o₂]!
    · rw [← hval] at htail₂
      exact ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₁)
        htail₁ ht₁ htail₂ ht₂
    · obtain ⟨σ, hg, hsp, hv⟩ := stabilizer_transitive hS hgsz hsymm hloop
        hcell₁ hne₁ ho₁ ho₂ (fun h => hval (by rw [h]))
      have hchild := stPerm_child hg hsp hS.it hcell₁ hne₁ ho₂ ho₁ hv
      have hUchild := iterOk_child hS.it hlvl hcell₁ hne₁ ho₁
      obtain ⟨W, q, hW, hq, hspW⟩ :=
        descPath_transport hg htail₁ hUchild hchild
      have hVW := ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₂)
        hW (hq.trans ht₁) htail₂ ht₂
      exact hVW.trans (hf hg
        (descends_iterOk htail₁.descends hUchild) hspW)

/-- Equal target histories below a cheap ancestor have equal partitions. -/
theorem descPath_ptn
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {level last : Nat} {st U V : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
    (hS : SubtreeOk ctx level st)
    (hU : DescPath ctx level st p₁ last U)
    (hV : DescPath ctx level st p₂ last V)
    (hp : p₂.map Prod.fst = p₁.map Prod.fst) : V.ptn = U.ptn :=
  descPath_invariant (fun _ st => st.ptn) (fun _ _ h => h.ptn.symm)
    hgsz hsymm hloop _ hS hU rfl hV hp

/-- Equal target histories below a cheap ancestor choose the same next
unhinted target, before either descent is discrete. -/
theorem descPath_target
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {level last : Nat} {st U V : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
    (hS : SubtreeOk ctx level st)
    (hU : DescPath ctx level st p₁ last U)
    (hV : DescPath ctx level st p₂ last V)
    (hp : p₂.map Prod.fst = p₁.map Prod.fst) (tcLevel : Nat) :
    specTargetcell ctx V.lab V.ptn last tcLevel =
      specTargetcell ctx U.lab U.ptn last tcLevel :=
  descPath_invariant (fun level st => specTargetcell ctx st.lab st.ptn level tcLevel)
    (fun hg hU hsp => stPerm_target hg hU hsp)
    hgsz hsymm hloop _ hS hU rfl hV hp

/-- Discrete descents below a cheap ancestor have the same depth and
leaf rows when the second target path is a prefix of the first. -/
theorem descPath_prefix
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (tcs : List Nat) :
    ∀ {level : Nat} {st : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
      {level₁ level₂ : Nat} {U V : RefineSt n},
      SubtreeOk ctx level st →
      DescPath ctx level st p₁ level₁ U →
      p₁.map Prod.fst = tcs →
      (∀ q, q < n → U.ptn[q]! ≤ level₁) →
      DescPath ctx level st p₂ level₂ V →
      p₂.map Prod.fst <+: tcs →
      (∀ q, q < n → V.ptn[q]! ≤ level₂) →
      level₂ = level₁ ∧ leafRows ctx V.lab = leafRows ctx U.lab := by
  induction tcs with
  | nil =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    have h1 : p₁ = [] := by
      cases p₁ with
      | nil => rfl
      | cons a l => simp at hp₁
    have h2 : p₂ = [] := by
      simpa using List.prefix_nil.mp hp₂
    subst h1
    subst h2
    obtain ⟨hl₁, hU'⟩ := descPath_nil hU
    obtain ⟨hl₂, hV'⟩ := descPath_nil hV
    subst hU'
    subst hV'
    exact ⟨by omega, rfl⟩
  | cons tc tcs' ih =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    cases p₁ with
    | nil => exact absurd hp₁ (by simp)
    | cons h₁ tl₁ =>
    obtain ⟨a₁, o₁⟩ := h₁
    rw [List.map_cons] at hp₁
    injection hp₁ with hh₁ ht₁
    have ha₁ : tc = a₁ := hh₁.symm
    subst ha₁
    cases hU with
    | step _ e₁ _ hlvl hcell₁ hne₁ ho₁ htail₁ =>
    cases p₂ with
    | nil =>
      obtain ⟨rfl, rfl⟩ := descPath_nil hV
      have hopen := target_open hS.it.ok.ptnSize hS.it.ok.ptnEnd
        hcell₁ tc (Nat.le_refl _) hne₁
      have hbound := target_end_lt hS.it.ok.ptnSize hS.it.ok.ptnEnd hcell₁
      have hclosed := hVd tc (by omega)
      omega
    | cons h₂ tl₂ =>
    obtain ⟨a₂, o₂⟩ := h₂
    rw [List.map_cons, List.cons_prefix_cons] at hp₂
    obtain ⟨hh₂, ht₂⟩ := hp₂
    have ha₂ : tc = a₂ := hh₂.symm
    subst ha₂
    cases hV with
    | step _ e₂ _ hlvl₂ hcell₂ hne₂ ho₂ htail₂ =>
    have hpsz := hS.it.ok.ptnSize
    have hend := hS.it.ok.ptnEnd
    have hee : e₁ = e₂ := cells_eq_of_start (by omega) hend
      hcell₁ hcell₂
    subst hee
    rcases Decidable.em (st.lab[tc + o₁]! = st.lab[tc + o₂]!) with
      hval | hval
    · -- the same child: recurse directly
      rw [← hval] at htail₂
      exact ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₁)
        htail₁ ht₁ hUd htail₂ ht₂ hVd
    · -- a deviation at this level, by the target's size
      have hflip := stabilizer_transitive hS hgsz hsymm hloop
        hcell₁ hne₁ ho₁ ho₂ (fun h => hval (by rw [h]))
      obtain ⟨σ, hgm, hspσ, hvv⟩ := hflip
      obtain ⟨W, qW, hdescW, hqW, hlrW, hptnW⟩ :=
        descPath_deviation_self hS.it hlvl hgm hspσ hcell₁ hne₁
          ho₁ ho₂ hvv htail₁ hUd
      have hWd : ∀ q, q < n → W.ptn[q]! ≤ level₁ := by
        intro q hq
        rw [hptnW]
        exact hUd q hq
      obtain ⟨hlev, hlr₂⟩ :=
        ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₂)
          hdescW (by rw [hqW, ht₁]) hWd htail₂ ht₂ hVd
      exact ⟨hlev, hlr₂.trans hlrW⟩

end Hex.GraphIso.Nauty
