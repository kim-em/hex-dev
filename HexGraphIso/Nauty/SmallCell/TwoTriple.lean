/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Exotic
import all HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Step
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
The two-triple configuration.

Under a defect-four cheapautom pass with two triple cells, the flip at
one triple may have to move the other triple as well. The constant
cross-count between the triples is `0`, `1`, `2` or `3`. The uniform
counts leave the other triple fixed and reduce to the bare
transposition, and the matched counts pair each member with its unique
minority partner, the transposition swapping the two partners along.
Everything is forced by counting exactly as in `SmallCell/Exotic`: the
reverse counts make the two partners distinct, and both triples'
internal structure is off-diagonally constant (`triple_internal`).
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

section TwoTriple

variable {st : RefineSt n} {level tc d2 oU oV : Nat}

set_option maxHeartbeats 4000000 in
/-- The cross-cell double swap: the two chosen members of the target
triple swap together with their partners in the other triple. -/
theorem twoTriple_sw2 {pa pb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (hpa : pa ≤ 2) (hpb : pb ≤ 2) (hpab : pa ≠ pb)
    (hfixT1 : ∀ w, w ≤ 2 → w ≠ oU → w ≠ oV →
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pb]!))
    (hfixT2 : ∀ w, w ≤ 2 → w ≠ pa → w ≠ pb →
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pb]!))
    (hc1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pa]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pb]!)
    (hc2 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pb]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pa]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the two windows are disjoint
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hin2 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[d2 + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (d2 + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[d2 + pa]! st.lab[d2 + pb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hin1 _ _ hoU hoV hne,
      hcross _ _ hoU hpa, hcross _ _ hoU hpb,
      hcross _ _ hoV hpa, hcross _ _ hoV hpb,
      hin2 _ _ hpa hpb hpab⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[d2 + pa]! →
      z ≠ st.lab[d2 + pb]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[d2 + pa]! =
        (ctx.g[z]!).mem st.lab[d2 + pb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := hfixT1 (j - tc) hw hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have hwa : j - d2 ≠ pa := fun hcon =>
        hzx (by rw [show j = d2 + pa by omega])
      have hwb : j - d2 ≠ pb := fun hcon =>
        hzy (by rw [show j = d2 + pb by omega])
      have h := hfixT2 (j - d2) hw hwa hwb
      rw [show d2 + (j - d2) = j by omega] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hT1 hpmem
          (o := oU) (o' := oV) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (tc + oU) (by omega)) hz,
          hsymm _ _ (hlb (tc + oV) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hT2 hpmem
          (o := pa) (o' := pb) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (d2 + pa) (by omega)) hz,
          hsymm _ _ (hlb (d2 + pb) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
  -- the swap permutes both triples within themselves
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
          st.lab[d2 + pb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have ho' : o < tc + 2 + 1 - tc := ho
      rcases Decidable.em (o = oU) with rfl | hou
      · refine ⟨oV, show oV < tc + 2 + 1 - tc by omega, ?_⟩
        rw [sw2_u]
      rcases Decidable.em (o = oV) with rfl | hov
      · refine ⟨oU, show oU < tc + 2 + 1 - tc by omega, ?_⟩
        rw [sw2_v hOk]
      · refine ⟨o, ho, sw2_fix (hin1 o oU (by omega) hoU hou)
          (hin1 o oV (by omega) hoV hov)
          (hcross o pa (by omega) hpa)
          (hcross o pb (by omega) hpb)⟩
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have ho' : o < d2 + 2 + 1 - d2 := ho
      rcases Decidable.em (o = pa) with rfl | hoa
      · refine ⟨pb, show pb < d2 + 2 + 1 - d2 by omega, ?_⟩
        rw [sw2_x hOk]
      rcases Decidable.em (o = pb) with rfl | hob
      · refine ⟨pa, show pa < d2 + 2 + 1 - d2 by omega, ?_⟩
        rw [sw2_y hOk]
      · refine ⟨o, ho, sw2_fix
          (fun h => hcross oU o hoU (by omega) h.symm)
          (fun h => hcross oV o hoV (by omega) h.symm)
          (hin2 o pa (by omega) hpa hoa)
          (hin2 o pb (by omega) hpb hob)⟩
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have ho1 : o = 0 := by omega
      have hbd : p.1 < n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hother1 : ∀ w' : Nat, w' ≤ 2 →
          st.lab[p.1 + o]! ≠ st.lab[tc + w']! := by
        intro w' hw' hcon
        have := hinj (p.1 + o) (tc + w') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpT1 (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hT1
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      have hother2 : ∀ w' : Nat, w' ≤ 2 →
          st.lab[p.1 + o]! ≠ st.lab[d2 + w']! := by
        intro w' hw' hcon
        have := hinj (p.1 + o) (d2 + w') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpT2 (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hT2
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw2_fix (hother1 oU hoU) (hother1 oV hoV)
        (hother2 pa hpa) (hother2 pb hpb)⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
      st.lab[d2 + pb]!) hIt hgsz
    (sw2_lt hOk) (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

private theorem three_one_ex {f : Nat → Nat}
    (h0 : f 0 ≤ 1) (h1 : f 1 ≤ 1) (h2 : f 2 ≤ 1)
    (hs : f 0 + f 1 + f 2 = 1) :
    ∃ p, p ≤ 2 ∧ f p = 1 ∧ ∀ q, q ≤ 2 → q ≠ p → f q = 0 := by
  rcases Decidable.em (f 0 = 1) with ha | ha
  · refine ⟨0, by omega, ha, fun q hq hqp => ?_⟩
    have : q = 1 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> omega
  rcases Decidable.em (f 1 = 1) with hb | hb
  · refine ⟨1, by omega, hb, fun q hq hqp => ?_⟩
    have : q = 0 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> omega
  · refine ⟨2, by omega, by omega, fun q hq hqp => ?_⟩
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> omega

private theorem three_zero_ex {f : Nat → Nat}
    (h0 : f 0 ≤ 1) (h1 : f 1 ≤ 1) (h2 : f 2 ≤ 1)
    (hs : f 0 + f 1 + f 2 = 2) :
    ∃ p, p ≤ 2 ∧ f p = 0 ∧ ∀ q, q ≤ 2 → q ≠ p → f q = 1 := by
  rcases Decidable.em (f 0 = 0) with ha | ha
  · refine ⟨0, by omega, ha, fun q hq hqp => ?_⟩
    have : q = 1 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> omega
  rcases Decidable.em (f 1 = 0) with hb | hb
  · refine ⟨1, by omega, hb, fun q hq hqp => ?_⟩
    have : q = 0 ∨ q = 2 := by omega
    rcases this with rfl | rfl <;> omega
  · refine ⟨2, by omega, by omega, fun q hq hqp => ?_⟩
    have : q = 0 ∨ q = 1 := by omega
    rcases this with rfl | rfl <;> omega

private theorem two_le_sum3 {f : Nat → Nat} {a b : Nat}
    (ha : a ≤ 2) (hb : b ≤ 2) (hne : a ≠ b) :
    f a + f b ≤ f 0 + f 1 + f 2 := by
  have h0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    omega

private theorem sum3_le_two_add {f : Nat → Nat} {a b : Nat}
    (hf0 : f 0 ≤ 1) (hf1 : f 1 ≤ 1) (hf2 : f 2 ≤ 1)
    (ha : a ≤ 2) (hb : b ≤ 2) (hne : a ≠ b) :
    f 0 + f 1 + f 2 ≤ f a + f b + 1 := by
  have h0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    omega

private theorem sum3_eq_of_cover {f : Nat → Nat} {a b c : Nat}
    (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f 0 + f 1 + f 2 = f a + f b + f c := by
  have h0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have h2 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;> omega

set_option maxHeartbeats 4000000 in
/-- The uniform cross-count route: the other triple's bits do not
distinguish the two chosen members, so the bare transposition
suffices. -/
theorem twoTriple_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (huni : ∀ q, q ≤ 2 →
      (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + q]! =
        (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + q]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have huv := hin1 _ _ hoU hoV hne
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := triple_internal hE hpsz hend hinj hlb hsymm hloop
        hT1 (j - tc) oU (j - tc) oV (by omega) (by omega) (by omega)
        (by omega) hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have h := huni (j - d2) hw
      rw [show d2 + (j - d2) = j by omega] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hT1 hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
      exact hconst
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    intro p hp o ho
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have ho' : o < tc + 2 + 1 - tc := ho
      rcases Decidable.em (o = oU) with rfl | hou
      · refine ⟨oV, show oV < tc + 2 + 1 - tc by omega, ?_⟩
        rw [sw1_u]
      rcases Decidable.em (o = oV) with rfl | hov
      · refine ⟨oU, show oU < tc + 2 + 1 - tc by omega, ?_⟩
        rw [sw1_v huv]
      · exact ⟨o, ho, sw1_fix (hin1 o oU (by omega) hoU hou)
          (hin1 o oV (by omega) hoV hov)⟩
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have ho' : o < d2 + 2 + 1 - d2 := ho
      exact ⟨o, ho, sw1_fix
        (fun h => hcross oU o hoU (by omega) h.symm)
        (fun h => hcross oV o hoV (by omega) h.symm)⟩
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have ho1 : o = 0 := by omega
      have hbd : p.1 < n := by
        have h1 := cells_bound (by rw [hpsz]; exact Nat.le_refl _)
          hend _ hp
        have h2 := cells_le _ hp
        rw [hpsz] at h1
        omega
      have hother1 : ∀ w' : Nat, w' ≤ 2 →
          st.lab[p.1 + o]! ≠ st.lab[tc + w']! := by
        intro w' hw' hcon
        have := hinj (p.1 + o) (tc + w') (by rw [ho1]; omega)
          (by omega) hcon
        rw [ho1] at this
        exact hpT1 (cells_eq_of_shared
          (by rw [hpsz]; exact Nat.le_refl _) hend hp hT1
          (j := p.1) (Nat.le_refl _) (by omega) (by omega) (by omega))
      exact ⟨o, ho, sw1_fix (hother1 oU hoU) (hother1 oV hoV)⟩
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The flip data at a triple target beside a second triple, all other
cells singletons: the constant cross-count is uniform (`0` or `3`,
reducing to the bare transposition) or matched (`1` or `2`, pairing
each chosen member with its unique minority partner and swapping the
partners along). -/
theorem twoTriple_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the forward rows: counts of target members into the other triple
  have hBrow : ∀ o, o ≤ 2 →
      (worksetOf n st.lab d2 (d2 + 2)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 2]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hT2
    rw [show d2 + 2 + 1 - d2 = 3 by omega, sum_range_three] at h
    exact h
  -- the reverse rows: counts of the other triple's members into the
  -- target
  have hRrow : ∀ q, q ≤ 2 →
      (worksetOf n st.lab tc (tc + 2)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 0]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 2]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hT1
    rw [show tc + 2 + 1 - tc = 3 by omega, sum_range_three] at h
    exact h
  have hBc : ∀ o o', o ≤ 2 → o' ≤ 2 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 2]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 2]! := by
    intro o o' ho ho'
    have h := hE _ hT1 _ hT2 o o' (by omega) (by omega)
    rw [hBrow o ho, hBrow o' ho'] at h
    exact h
  have hRc : ∀ q q', q ≤ 2 → q' ≤ 2 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 0]! +
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 1]! +
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 2]! =
      bitCnt ctx.g[st.lab[d2 + q']!]! st.lab[tc + 0]! +
      bitCnt ctx.g[st.lab[d2 + q']!]! st.lab[tc + 1]! +
      bitCnt ctx.g[st.lab[d2 + q']!]! st.lab[tc + 2]! := by
    intro q q' hq hq'
    have h := hE _ hT2 _ hT1 q q' (by omega) (by omega)
    rw [hRrow q hq, hRrow q' hq'] at h
    exact h
  -- symmetry between the atom bases
  have hBR : ∀ o q, o ≤ 2 → q ≤ 2 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! := by
    intro o q ho hq
    exact bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega))
      (hlb _ (by omega)))
  have hble : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  have hrle : ∀ q o : Nat,
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! ≤ 1 :=
    fun q o => bitCnt_le_one _ _
  -- the target-row sum classifies the configuration
  have hs4 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 2]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 2]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 2]! = 2 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 2]! = 3 := by
    have := hble oU 0
    have := hble oU 1
    have := hble oU 2
    omega
  have hVsum := hBc oU oV hoU hoV
  rcases hs4 with hs | hs | hs | hs
  · -- uniform empty
    refine twoTriple_sw1 hIt hgsz hsymm hloop hE hT1 hT2 hT12
      hsing hoU hoV hne ?_
    intro q hq
    have hq3 : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    have hu0 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + q]! =
        0 := by
      rcases hq3 with rfl | rfl | rfl <;> omega
    have hv0 : bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + q]! =
        0 := by
      have h1 := hble oV 0
      have h2 := hble oV 1
      have h3 := hble oV 2
      rcases hq3 with rfl | rfl | rfl <;> omega
    rw [bitCnt_eq_zero.mp hu0, bitCnt_eq_zero.mp hv0]
  · -- matched with one neighbour each
    obtain ⟨pu, hpu, hpu1, hpuz⟩ := three_one_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + oU]!]!
        st.lab[d2 + q]!) (hble oU 0) (hble oU 1) (hble oU 2) hs
    obtain ⟨pv, hpv, hpv1, hpvz⟩ := three_one_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + oV]!]!
        st.lab[d2 + q]!) (hble oV 0) (hble oV 1) (hble oV 2)
      (by omega)
    -- distinct partners: a shared partner would overload its row
    have hpuv : pu ≠ pv := by
      intro hcon
      have hq1 : (pu + 1) % 3 ≤ 2 := by omega
      have hq1p : (pu + 1) % 3 ≠ pu := by omega
      have hlow := two_le_sum3
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pu]!]!
          st.lab[tc + w]!) hoU hoV hne
      have hup := sum3_le_two_add
        (f := fun w => bitCnt ctx.g[st.lab[d2 + ((pu + 1) % 3)]!]!
          st.lab[tc + w]!) (hrle _ 0) (hrle _ 1) (hrle _ 2)
        hoU hoV hne
      have e1 := hBR oU pu hoU hpu
      have e2 := hBR oV pu hoV (by omega)
      have e3 := hBR oU ((pu + 1) % 3) hoU hq1
      have e4 := hBR oV ((pu + 1) % 3) hoV hq1
      have hz1 := hpuz ((pu + 1) % 3) hq1 hq1p
      have hz2 := hpvz ((pu + 1) % 3) hq1 (by omega)
      have hrc := hRc pu ((pu + 1) % 3) hpu hq1
      rw [← hcon] at hpv1
      omega
    -- the third member's partner avoids both
    have hoW : 3 - oU - oV ≤ 2 := by omega
    have hWu : 3 - oU - oV ≠ oU := by omega
    have hWv : 3 - oU - oV ≠ oV := by omega
    obtain ⟨pw, hpw, hpw1, hpwz⟩ := three_one_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + (3 - oU - oV)]!]!
        st.lab[d2 + q]!) (hble _ 0) (hble _ 1) (hble _ 2)
      (by have := hBc oU (3 - oU - oV) hoU hoW; omega)
    have hq2 : 3 - pu - pv ≤ 2 := by omega
    have hq2u : 3 - pu - pv ≠ pu := by omega
    have hq2v : 3 - pu - pv ≠ pv := by omega
    have hpwu : pw ≠ pu := by
      intro hcon
      have hlow := two_le_sum3
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pu]!]!
          st.lab[tc + w]!) (a := oU) (b := 3 - oU - oV) hoU hoW
        (fun h => hWu h.symm)
      have hcover := sum3_eq_of_cover
        (f := fun w => bitCnt ctx.g[st.lab[d2 + (3 - pu - pv)]!]!
          st.lab[tc + w]!) hoU hoV hoW hne (fun h => hWu h.symm)
        (fun h => hWv h.symm)
      have e1 := hBR oU pu hoU hpu
      have e2 := hBR (3 - oU - oV) pu hoW hpu
      have e3 := hBR oU (3 - pu - pv) hoU hq2
      have e4 := hBR oV (3 - pu - pv) hoV hq2
      have e5 := hBR (3 - oU - oV) (3 - pu - pv) hoW hq2
      have hz1 := hpuz (3 - pu - pv) hq2 hq2u
      have hz2 := hpvz (3 - pu - pv) hq2 hq2v
      have hz3 := hpwz (3 - pu - pv) hq2 (by omega)
      have hrc := hRc pu (3 - pu - pv) hpu hq2
      rw [hcon] at hpw1
      omega
    have hpwv : pw ≠ pv := by
      intro hcon
      have hlow := two_le_sum3
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pv]!]!
          st.lab[tc + w]!) (a := oV) (b := 3 - oU - oV) hoV hoW
        (fun h => hWv h.symm)
      have hcover := sum3_eq_of_cover
        (f := fun w => bitCnt ctx.g[st.lab[d2 + (3 - pu - pv)]!]!
          st.lab[tc + w]!) hoU hoV hoW hne (fun h => hWu h.symm)
        (fun h => hWv h.symm)
      have e1 := hBR oV pv hoV hpv
      have e2 := hBR (3 - oU - oV) pv hoW hpv
      have e3 := hBR oU (3 - pu - pv) hoU hq2
      have e4 := hBR oV (3 - pu - pv) hoV hq2
      have e5 := hBR (3 - oU - oV) (3 - pu - pv) hoW hq2
      have hz1 := hpuz (3 - pu - pv) hq2 hq2u
      have hz2 := hpvz (3 - pu - pv) hq2 hq2v
      have hz3 := hpwz (3 - pu - pv) hq2 (by omega)
      have hrc := hRc pv (3 - pu - pv) hpv hq2
      rw [hcon] at hpw1
      omega
    refine twoTriple_sw2 hIt hgsz hsymm hloop hE hT1 hT2 hT12
      hsing hoU hoV hne hpu hpv hpuv ?_ ?_ ?_ ?_
    · -- the third target member has equal bits at the partner pair
      intro w hw hwu hwv
      have hwW : w = 3 - oU - oV := by omega
      constructor
      · have h := triple_internal hE hpsz hend hinj hlb hsymm
          hloop hT1 w oU w oV (by omega) (by omega) (by omega)
          (by omega) hwu hwv
        exact h
      · rw [hwW]
        have hz1 := hpwz pu hpu (fun h => hpwu h.symm)
        have hz2 := hpwz pv hpv (fun h => hpwv h.symm)
        rw [bitCnt_eq_zero.mp hz1, bitCnt_eq_zero.mp hz2]
    · -- the third partner has equal bits at the chosen pair
      intro w hw hwa hwb
      constructor
      · have hz1 := hpuz w hw hwa
        have hz2 := hpvz w hw hwb
        have e1 := hBR oU w hoU hw
        have e2 := hBR oV w hoV hw
        have hzz1 : bitCnt ctx.g[st.lab[d2 + w]!]!
            st.lab[tc + oU]! = 0 := by omega
        have hzz2 : bitCnt ctx.g[st.lab[d2 + w]!]!
            st.lab[tc + oV]! = 0 := by omega
        rw [bitCnt_eq_zero.mp hzz1, bitCnt_eq_zero.mp hzz2]
      · exact triple_internal hE hpsz hend hinj hlb hsymm hloop
          hT2 w pu w pv (by omega) (by omega) (by omega)
          (by omega) (fun h => hwa h) (fun h => hwb h)
    · -- the matched cross bits
      have e1 := hBR oU pu hoU hpu
      have hb1 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + pu]! =
          1 := hpu1
      rw [bitCnt_eq_one.mp hb1, bitCnt_eq_one.mp hpv1]
    · have hz1 := hpuz pv hpv hpuv.symm
      have hz2 := hpvz pu hpu hpuv
      rw [bitCnt_eq_zero.mp hz1, bitCnt_eq_zero.mp hz2]
  · -- matched with one non-neighbour each
    obtain ⟨pu, hpu, hpu1, hpuz⟩ := three_zero_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + oU]!]!
        st.lab[d2 + q]!) (hble oU 0) (hble oU 1) (hble oU 2) hs
    obtain ⟨pv, hpv, hpv1, hpvz⟩ := three_zero_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + oV]!]!
        st.lab[d2 + q]!) (hble oV 0) (hble oV 1) (hble oV 2)
      (by omega)
    have hpuv : pu ≠ pv := by
      intro hcon
      have hq1 : (pu + 1) % 3 ≤ 2 := by omega
      have hq1p : (pu + 1) % 3 ≠ pu := by omega
      have hup := sum3_le_two_add
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pu]!]!
          st.lab[tc + w]!) (hrle _ 0) (hrle _ 1) (hrle _ 2)
        hoU hoV hne
      have hlow := two_le_sum3
        (f := fun w => bitCnt ctx.g[st.lab[d2 + ((pu + 1) % 3)]!]!
          st.lab[tc + w]!) hoU hoV hne
      have e1 := hBR oU pu hoU hpu
      have e2 := hBR oV pu hoV (by omega)
      have e3 := hBR oU ((pu + 1) % 3) hoU hq1
      have e4 := hBR oV ((pu + 1) % 3) hoV hq1
      have hz1 := hpuz ((pu + 1) % 3) hq1 hq1p
      have hz2 := hpvz ((pu + 1) % 3) hq1 (by omega)
      have hrc := hRc pu ((pu + 1) % 3) hpu hq1
      rw [← hcon] at hpv1
      omega
    have hoW : 3 - oU - oV ≤ 2 := by omega
    have hWu : 3 - oU - oV ≠ oU := by omega
    have hWv : 3 - oU - oV ≠ oV := by omega
    obtain ⟨pw, hpw, hpw1, hpwz⟩ := three_zero_ex
      (f := fun q => bitCnt ctx.g[st.lab[tc + (3 - oU - oV)]!]!
        st.lab[d2 + q]!) (hble _ 0) (hble _ 1) (hble _ 2)
      (by have := hBc oU (3 - oU - oV) hoU hoW; omega)
    have hq2 : 3 - pu - pv ≤ 2 := by omega
    have hq2u : 3 - pu - pv ≠ pu := by omega
    have hq2v : 3 - pu - pv ≠ pv := by omega
    have hpwu : pw ≠ pu := by
      intro hcon
      have hup := sum3_le_two_add
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pu]!]!
          st.lab[tc + w]!) (hrle _ 0) (hrle _ 1) (hrle _ 2)
        (a := oU) (b := 3 - oU - oV) hoU hoW (fun h => hWu h.symm)
      have hcover := sum3_eq_of_cover
        (f := fun w => bitCnt ctx.g[st.lab[d2 + (3 - pu - pv)]!]!
          st.lab[tc + w]!) hoU hoV hoW hne (fun h => hWu h.symm)
        (fun h => hWv h.symm)
      have e1 := hBR oU pu hoU hpu
      have e2 := hBR (3 - oU - oV) pu hoW hpu
      have e3 := hBR oU (3 - pu - pv) hoU hq2
      have e4 := hBR oV (3 - pu - pv) hoV hq2
      have e5 := hBR (3 - oU - oV) (3 - pu - pv) hoW hq2
      have hz1 := hpuz (3 - pu - pv) hq2 hq2u
      have hz2 := hpvz (3 - pu - pv) hq2 hq2v
      have hz3 := hpwz (3 - pu - pv) hq2 (by omega)
      have hrc := hRc pu (3 - pu - pv) hpu hq2
      rw [hcon] at hpw1
      omega
    have hpwv : pw ≠ pv := by
      intro hcon
      have hup := sum3_le_two_add
        (f := fun w => bitCnt ctx.g[st.lab[d2 + pv]!]!
          st.lab[tc + w]!) (hrle _ 0) (hrle _ 1) (hrle _ 2)
        (a := oV) (b := 3 - oU - oV) hoV hoW (fun h => hWv h.symm)
      have hcover := sum3_eq_of_cover
        (f := fun w => bitCnt ctx.g[st.lab[d2 + (3 - pu - pv)]!]!
          st.lab[tc + w]!) hoU hoV hoW hne (fun h => hWu h.symm)
        (fun h => hWv h.symm)
      have e1 := hBR oV pv hoV hpv
      have e2 := hBR (3 - oU - oV) pv hoW hpv
      have e3 := hBR oU (3 - pu - pv) hoU hq2
      have e4 := hBR oV (3 - pu - pv) hoV hq2
      have e5 := hBR (3 - oU - oV) (3 - pu - pv) hoW hq2
      have hz1 := hpuz (3 - pu - pv) hq2 hq2u
      have hz2 := hpvz (3 - pu - pv) hq2 hq2v
      have hz3 := hpwz (3 - pu - pv) hq2 (by omega)
      have hrc := hRc pv (3 - pu - pv) hpv hq2
      rw [hcon] at hpw1
      omega
    refine twoTriple_sw2 hIt hgsz hsymm hloop hE hT1 hT2 hT12
      hsing hoU hoV hne hpu hpv hpuv ?_ ?_ ?_ ?_
    · intro w hw hwu hwv
      have hwW : w = 3 - oU - oV := by omega
      constructor
      · exact triple_internal hE hpsz hend hinj hlb hsymm
          hloop hT1 w oU w oV (by omega) (by omega) (by omega)
          (by omega) hwu hwv
      · rw [hwW]
        have hz1 := hpwz pu hpu (fun h => hpwu h.symm)
        have hz2 := hpwz pv hpv (fun h => hpwv h.symm)
        rw [bitCnt_eq_one.mp hz1, bitCnt_eq_one.mp hz2]
    · intro w hw hwa hwb
      constructor
      · have hz1 := hpuz w hw hwa
        have hz2 := hpvz w hw hwb
        have e1 := hBR oU w hoU hw
        have e2 := hBR oV w hoV hw
        have hzz1 : bitCnt ctx.g[st.lab[d2 + w]!]!
            st.lab[tc + oU]! = 1 := by omega
        have hzz2 : bitCnt ctx.g[st.lab[d2 + w]!]!
            st.lab[tc + oV]! = 1 := by omega
        rw [bitCnt_eq_one.mp hzz1, bitCnt_eq_one.mp hzz2]
      · exact triple_internal hE hpsz hend hinj hlb hsymm hloop
          hT2 w pu w pv (by omega) (by omega) (by omega)
          (by omega) (fun h => hwa h) (fun h => hwb h)
    · rw [bitCnt_eq_zero.mp hpu1, bitCnt_eq_zero.mp hpv1]
    · have hz1 := hpuz pv hpv hpuv.symm
      have hz2 := hpvz pu hpu hpuv
      rw [bitCnt_eq_one.mp hz1, bitCnt_eq_one.mp hz2]
  · -- uniform complete
    refine twoTriple_sw1 hIt hgsz hsymm hloop hE hT1 hT2 hT12
      hsing hoU hoV hne ?_
    intro q hq
    have hq3 : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    have hu1 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + q]! =
        1 := by
      have h1 := hble oU 0
      have h2 := hble oU 1
      have h3 := hble oU 2
      rcases hq3 with rfl | rfl | rfl <;> omega
    have hv1 : bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + q]! =
        1 := by
      have h1 := hble oV 0
      have h2 := hble oV 1
      have h3 := hble oV 2
      rcases hq3 with rfl | rfl | rfl <;> omega
    rw [bitCnt_eq_one.mp hu1, bitCnt_eq_one.mp hv1]

end TwoTriple

end Hex.GraphIso.Nauty
