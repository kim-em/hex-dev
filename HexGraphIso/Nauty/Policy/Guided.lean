/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Positions
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Policy.Selection
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- A live first-reference descent uses either the canonical target rule
or the saved first target at each level. -/
def Guided (ctx : Ctx n) (tcLevel : Nat) (store : Array Int) :
    Nat → RefineSt n → List (Nat × Nat) → Prop
  | _, _, [] => True
  | level, st, (tc, o) :: path =>
    (specTargetcell ctx st.lab st.ptn level tcLevel = tc ∨ store[level]! = Int.ofNat tc) ∧
      Guided ctx tcLevel store (level + 1) (childSt ctx level st tc st.lab[tc + o]!) path

/-- Two discrete descents to the same labelling have the same depth when
one records canonical targets and the other uses canonical or saved targets.
The final labelling fixes their chosen vertices at every common target. -/
theorem Guided.depth {ctx : Ctx n} {tcLevel base last₁ last₂ : Nat}
    {store : Array Int} {root first current : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
    (hfirst : DescPath ctx base root p₁ last₁ first)
    (hok : IterOk ctx base root) (hselect : Selects ctx tcLevel base root p₁)
    (htarget : Targets store base (p₁.map Prod.fst))
    (hcurrent : DescPath ctx base root p₂ last₂ current)
    (hguided : Guided ctx tcLevel store base root p₂)
    (hdisc₁ : ∀ q, q < n → first.ptn[q]! ≤ last₁)
    (hdisc₂ : ∀ q, q < n → current.ptn[q]! ≤ last₂)
    (hlab : first.lab = current.lab) : last₂ = last₁ := by
  induction hfirst generalizing p₂ last₂ current with
  | refl base root =>
    cases hcurrent with
    | refl => rfl
    | step tc e o hlvl hcell hne ho htail =>
      have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
      have hopen := target_open hok.ok.ptnSize hok.ok.ptnEnd hcell tc (Nat.le_refl _) hne
      have hclosed := hdisc₁ tc (by omega)
      omega
  | @step base last₁ root first path tc e o hlvl hcell hne ho htail ih =>
    cases p₂ with
    | nil =>
      obtain ⟨rfl, rfl⟩ := descPath_nil hcurrent
      have he := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
      have hopen := target_open hok.ok.ptnSize hok.ok.ptnEnd hcell tc (Nat.le_refl _) hne
      have hclosed := hdisc₂ tc (by omega)
      omega
    | cons pick path₂ =>
      obtain ⟨tc₂, o₂⟩ := pick
      have htc : tc₂ = tc := by
        rcases hguided.1 with hspec | hstored
        · exact hspec.symm.trans hselect.1
        · change store[base]! = Int.ofNat tc₂ at hstored
          have hfirstTc : store[base]! = Int.ofNat tc := htarget 0 (by simp)
          exact Int.ofNat.inj (hstored.symm.trans hfirstTc)
      subst tc₂
      have hp₂ := hcurrent.picked hok
      cases hcurrent with
      | step _ e₂ _ hlvl₂ hcell₂ hne₂ ho₂ htail₂ =>
        have hp₁ := (DescPath.step tc e o hlvl hcell hne ho htail).picked hok
        have he₁ := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell
        have he₂ := target_end_lt hok.ok.ptnSize hok.ok.ptnEnd hcell₂
        have hval : root.lab[tc + o]! = root.lab[tc + o₂]! := by
          rw [← hp₁, hlab, hp₂]
        have hinj := hok.inj
        unfold LabInj at hinj
        have hindices := hinj (tc + o) (tc + o₂) (by omega) (by omega) hval
        have hoff : o₂ = o := by omega
        subst o₂
        have htargets : Targets store (base + 1) (path.map Prod.fst) := by
          simpa only [List.map_cons, List.drop_succ_cons, List.drop_zero] using htarget.drop 1
        exact ih (iterOk_child hok hlvl hcell hne ho) hselect.2 htargets
          htail₂ hguided.2 hdisc₁ hdisc₂ hlab

end Hex.GraphIso.Nauty
