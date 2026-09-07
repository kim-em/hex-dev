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
