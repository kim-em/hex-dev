/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellExotic3
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.SmallCellLeaves

public section

/-!
All leaves below a cheapautom node (SPEC § Verified search
refinement, the code-1 arm of the store-validity obligation).

A passing guard leaves the node in one of two shapes, and this file
turns either into the flip data every deviation consumes:
`flipData_of_subtreeOk` reads a pair or triple target off the
first-branch shape, and a target of any size at most five off a
defect of at most four, where the exotic analogues apply. The
all-leaves induction then walks a target-position path, recursing on
equal choices and gluing one deviation at a differing choice.

The file sits above the exotic layer because that is where the
defect-four flip data is proved; everything else the induction needs
lives in `SmallCellLeaves`.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Flip data from the node shape -/

/-- Flip data at any cell of a node satisfying the invariant. The
first-branch shape names a pair or triple target; a defect of at most
four bounds every cell at five positions and hands the target to the
exotic analogues. -/
theorem flipData_of_subtreeOk {st : RefineSt n} {level tc te oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : (tc, te) ∈ cells st.ptn level n) (hne : tc < te)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hone : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  rcases hS.shape with hsmall | hdef
  · rcases hsmall _ hcell with hsz2 | ⟨hsz3, huniq⟩
    · -- a pair target
      have hsz2' : te + 1 - tc ≤ 2 := hsz2
      have he : te = tc + 1 := by omega
      subst he
      have hOdd : ∀ q ∈ cells st.ptn level n,
          q.2 ≠ q.1 + 1 → (q.2 + 1 - q.1) % 2 = 1 := by
        intro q hq hqne
        have hqle := cells_le _ hq
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · have h1 : q.2 + 1 - q.1 = 1 := by omega
          omega
        · omega
      exact pair_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hOdd (by omega) (by omega) hone
    · -- the triple target
      have hsz3' : te + 1 - tc = 3 := hsz3
      have he : te = tc + 2 := by omega
      subst he
      have hsmall' : ∀ q ∈ cells st.ptn level n,
          q ≠ (tc, tc + 2) → q.2 + 1 - q.1 ≤ 2 := by
        intro q hq hqne
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · exact h2
        · exact absurd (huniq q hq h3) hqne
      exact triple_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hsmall' (by omega) (by omega) hone
  · -- the exotic shapes
    exact defect4_flip_data hS.it hgsz hsymm hloop hS.eqt hdef
      hcell hoU hoV hone

/-! # All leaves below a cheapautom node have equal rows -/

/-- Any two discrete descents below a first-branch node choosing the
same target cells have equal leaf rows: equal choices recurse, and a
differing choice is one pair or triple deviation glued to the
transported deeper path. -/
theorem descPath_leafRows_all
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
      p₂.map Prod.fst = tcs →
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
      cases p₂ with
      | nil => rfl
      | cons a l => simp at hp₂
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
    cases p₂ with
    | nil => exact absurd hp₂ (by simp)
    | cons h₂ tl₂ =>
    obtain ⟨a₁, o₁⟩ := h₁
    obtain ⟨a₂, o₂⟩ := h₂
    rw [List.map_cons] at hp₁ hp₂
    injection hp₁ with hh₁ ht₁
    injection hp₂ with hh₂ ht₂
    have ha₁ : tc = a₁ := hh₁.symm
    subst ha₁
    have ha₂ : tc = a₂ := hh₂.symm
    subst ha₂
    cases hU with
    | step _ e₁ _ hlvl hcell₁ hne₁ ho₁ htail₁ =>
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
      have hflip := flipData_of_subtreeOk hS hgsz hsymm hloop
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
