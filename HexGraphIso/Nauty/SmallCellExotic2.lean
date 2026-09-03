/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellExotic
import all HexGraphIso.Nauty.Equitable

public section

/-!
The two-triple configuration (SPEC § Verified search refinement, the
code-1 arm of the store-validity obligation).

Under a defect-four cheapautom pass with two triple cells, the flip at
either triple couples across to the other: the constant cross-counts
between the triples are `0`, `1`, `2` or `3`; the uniform counts leave
the other triple fixed and reduce to the bare transposition, and the
matched counts pair each member with its unique minority partner, the
transposition swapping the two partners along. Everything is forced by
counting exactly as in the lone-cell file: the reverse counts make the
two partners distinct, and both triples' internal structure is
off-diagonally constant (`triple_internal`).
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

private theorem sum_range_succ' (f : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map f).sum =
      ((List.range m).map f).sum + f m := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

private theorem sum_range_three' (f : Nat → Nat) :
    ((List.range 3).map f).sum = f 0 + f 1 + f 2 := by
  rw [show (3 : Nat) = 2 + 1 from rfl, sum_range_succ',
    show (2 : Nat) = 1 + 1 from rfl, sum_range_succ',
    show (1 : Nat) = 0 + 1 from rfl, sum_range_succ']
  simp

section TwoTriple

variable {st : RefineSt} {level tc d2 oU oV : Nat}

set_option maxHeartbeats 4000000 in
/-- The cross-cell double swap: the two chosen members of the target
triple swap together with their partners in the other triple. -/
theorem twoTriple_sw2 {pa pb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = ctx.n)
    (hg : ∀ w, w < ctx.n → ctx.g[w]! < 2 ^ ctx.n)
    (hsymm : ∀ z w, z < ctx.n → w < ctx.n →
      (ctx.g[z]!).testBit w = (ctx.g[w]!).testBit z)
    (hloop : ∀ z, z < ctx.n → (ctx.g[z]!).testBit z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level ctx.n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level ctx.n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level ctx.n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (hpa : pa ≤ 2) (hpb : pb ≤ 2) (hpab : pa ≠ pb)
    (hfixT1 : ∀ w, w ≤ 2 → w ≠ oU → w ≠ oV →
      ((ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).testBit st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[tc + w]!]!).testBit st.lab[d2 + pa]! =
        (ctx.g[st.lab[tc + w]!]!).testBit st.lab[d2 + pb]!))
    (hfixT2 : ∀ w, w ≤ 2 → w ≠ pa → w ≠ pb →
      ((ctx.g[st.lab[d2 + w]!]!).testBit st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + w]!]!).testBit st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[d2 + w]!]!).testBit st.lab[d2 + pa]! =
        (ctx.g[st.lab[d2 + w]!]!).testBit st.lab[d2 + pb]!))
    (hc1 : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[d2 + pa]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[d2 + pb]!)
    (hc2 : (ctx.g[st.lab[tc + oU]!]!).testBit st.lab[d2 + pb]! =
      (ctx.g[st.lab[tc + oV]!]!).testBit st.lab[d2 + pa]!) :
    ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < ctx.n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < ctx.n → st.lab[i]! < ctx.n := fun i hi =>
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
  have hOk : Sw2Ok ctx.n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[d2 + pa]! st.lab[d2 + pb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hin1 _ _ hoU hoV hne,
      hcross _ _ hoU hpa, hcross _ _ hoU hpb,
      hcross _ _ hoV hpa, hcross _ _ hoV hpb,
      hin2 _ _ hpa hpb hpab⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < ctx.n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[d2 + pa]! →
      z ≠ st.lab[d2 + pb]! →
      (ctx.g[z]!).testBit st.lab[tc + oU]! =
        (ctx.g[z]!).testBit st.lab[tc + oV]! ∧
      (ctx.g[z]!).testBit st.lab[d2 + pa]! =
        (ctx.g[z]!).testBit st.lab[d2 + pb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := ctx.n) j (by omega)
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
      have hpmem : (p.1, p.1) ∈ cells st.ptn level ctx.n := by
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
  have hset : ∀ p ∈ cells st.ptn level ctx.n,
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
      have hbd : p.1 < ctx.n := by
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
      st.lab[d2 + pb]!) hIt hgsz hg
    (sw2_lt hOk) (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

end TwoTriple

end Hex.GraphIso.Nauty
