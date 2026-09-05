/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Step

public section

/-!
The equitability fixpoint theorem (SPEC § Verified search refinement,
the cheapautom clause of the store-validity obligation).

`HexGraphIso.Nauty.Equitable.Basic` defines the predicates and proves the
per-pass postconditions; this file proves the certificate invariant's
preservation across a refinement step and assembles `refine_equitable`:
when `refine` exits with its active set exhausted, the partition is
equitable.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # Containment algebra and cell uniqueness for the certificate

Containment of `a` in `b` is written `a.inter b = a`, the form the
certificate invariant uses for `V.inter (activeUnion …) = V`. -/

private theorem mem_of_inter_eq {a b : VSet n} (h : a.inter b = a) {i : Nat}
    (ha : a.mem i = true) : b.mem i = true :=
  VSet.subset_iff.mp (VSet.subset_iff_inter.mpr h) i ha

private theorem inter_eq_of_mem {a b : VSet n}
    (h : ∀ i, a.mem i = true → b.mem i = true) : a.inter b = a :=
  VSet.subset_iff_inter.mp (VSet.subset_iff.mpr h)

private theorem mem_inter_empty {a b : VSet n} (h : a.inter b = VSet.empty)
    {i : Nat} (ha : a.mem i = true) : b.mem i = false := by
  have := congrArg (fun s => s.mem i) h
  simp only [VSet.mem_inter, VSet.mem_empty, ha, Bool.true_and] at this
  exact this

private theorem inter_empty_of_mem {a b : VSet n}
    (h : ∀ i, a.mem i = true → b.mem i = false) : a.inter b = VSet.empty :=
  VSet.ext fun i => by
    rw [VSet.mem_inter, VSet.mem_empty]
    rcases ha : a.mem i with _ | _
    · rfl
    · rw [h i ha]
      rfl

private theorem sub_or_xor {a b : VSet n} (h : a.inter b = a) :
    a.union (b.xor a) = b :=
  VSet.ext fun i => by
    rw [VSet.mem_union, VSet.mem_xor]
    rcases ha : a.mem i with _ | _
    · cases b.mem i <;> rfl
    · rw [mem_of_inter_eq h ha]
      rfl

private theorem xor_and_self {a b : VSet n} (h : a.inter b = a) :
    (b.xor a).inter a = VSet.empty :=
  inter_empty_of_mem fun i hi => by
    rw [VSet.mem_xor] at hi
    rcases ha : a.mem i with _ | _
    · rfl
    · rw [mem_of_inter_eq h ha, ha] at hi
      cases hi

private theorem xor_submask {a b : VSet n} (h : a.inter b = a) :
    (b.xor a).inter b = b.xor a :=
  inter_eq_of_mem fun i hi => by
    rw [VSet.mem_xor] at hi
    rcases hb : b.mem i with _ | _
    · rcases ha : a.mem i with _ | _
      · rw [ha, hb] at hi
        cases hi
      · rw [mem_of_inter_eq h ha] at hb
        cases hb
    · rfl

private theorem submask_or {a b c : VSet n} (h : a.inter c = a) :
    a.inter (b.union c) = a :=
  inter_eq_of_mem fun i hi => by
    rw [VSet.mem_union, mem_of_inter_eq h hi, Bool.or_true]

private theorem or_submask_of {a b c : VSet n} (ha : a.inter c = a)
    (hb : b.inter c = b) : (a.union b).inter c = a.union b :=
  inter_eq_of_mem fun i hi => by
    rw [VSet.mem_union] at hi
    rcases h1 : a.mem i with _ | _
    · rw [h1, Bool.false_or] at hi
      exact mem_of_inter_eq hb hi
    · exact mem_of_inter_eq ha h1

private theorem and_or_zero {a b c : VSet n} (hab : a.inter b = VSet.empty)
    (hac : a.inter c = VSet.empty) : a.inter (b.union c) = VSet.empty :=
  inter_empty_of_mem fun i hi => by
    rw [VSet.mem_union, mem_inter_empty hab hi, mem_inter_empty hac hi]
    rfl

/-- Two maximal runs of the same partition are equal or disjoint. -/
theorem isCell_disj_or_eq {ptn : Array Nat} {level a la b lb : Nat}
    (ha : IsCell ptn level a la) (hb : IsCell ptn level b lb) :
    (a = b ∧ la = lb) ∨ a + la ≤ b ∨ b + lb ≤ a := by
  rcases Decidable.em (a + la ≤ b) with h1 | h1
  · exact Or.inr (Or.inl h1)
  · rcases Decidable.em (b + lb ≤ a) with h2 | h2
    · exact Or.inr (Or.inr h2)
    · refine Or.inl ?_
      have hstart : a = b := by
        rcases Nat.lt_trichotomy a b with hlt | heq | hgt
        · exfalso
          have hint := ha.2.2.1 (b - 1) (by omega) (by
            have := hb.1
            omega)
          rcases hb.2.1 with h0 | hbd
          · omega
          · omega
        · exact heq
        · exfalso
          have hint := hb.2.2.1 (a - 1) (by omega) (by
            have := ha.1
            omega)
          rcases ha.2.1 with h0 | had
          · omega
          · omega
      subst hstart
      have hlen : la = lb := by
        rcases Nat.lt_trichotomy la lb with hlt | heq | hgt
        · exfalso
          have hint := hb.2.2.1 (a + la - 1) (by
            have := ha.1
            omega) (by omega)
          have hend := ha.2.2.2
          omega
        · exact heq
        · exfalso
          have hint := ha.2.2.1 (a + lb - 1) (by
            have := hb.1
            omega) (by omega)
          have hend := hb.2.2.2
          omega
      exact ⟨rfl, hlen⟩

/-- A nested window's splitter set lies inside the enclosing one. -/
private theorem worksetOf_nested {lab : Array Nat} {a b a' b' : Nat}
    (h1 : a ≤ a') (h2 : b' ≤ b) (h3 : a' ≤ b') :
    (worksetOf n lab a' b').inter (worksetOf n lab a b) =
      worksetOf n lab a' b' := by
  refine inter_eq_of_mem fun v hv => ?_
  obtain ⟨hvn, hm⟩ := mem_worksetOf_iff.mp hv
  refine mem_worksetOf_iff.mpr ⟨hvn, ?_⟩
  obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hm
  exact mem_segN_iff.mpr ⟨a' - a + o, by omega, by
    rw [show a + (a' - a + o) = a' + o from by omega]⟩

private theorem submask_trans {x y z : VSet n} (h1 : x.inter y = x)
    (h2 : y.inter z = y) : x.inter z = x :=
  inter_eq_of_mem fun _ hi =>
    mem_of_inter_eq h2 (mem_of_inter_eq h1 hi)

private theorem zero_of_and_submask {a u v : VSet n} (h1 : a.inter u = VSet.empty)
    (h2 : v.inter u = v) : a.inter v = VSet.empty :=
  inter_empty_of_mem fun i ha => by
    rcases hv : v.mem i with _ | _
    · rfl
    · have hu := mem_of_inter_eq h2 hv
      rw [mem_inter_empty h1 ha] at hu
      cases hu

private theorem submask_xor_of {x a b : VSet n} (hxb : x.inter b = x)
    (hxa : x.inter a = VSet.empty) : x.inter (b.xor a) = x :=
  inter_eq_of_mem fun i hi => by
    rw [VSet.mem_xor, mem_of_inter_eq hxb hi, mem_inter_empty hxa hi]
    rfl

private theorem submask_or_left {a b c : VSet n} (h : a.inter b = a) :
    a.inter (b.union c) = a :=
  inter_eq_of_mem fun _ hi => by
    rw [VSet.mem_union, mem_of_inter_eq h hi, Bool.true_or]

private theorem sub_and_zero {x e d : VSet n} (h1 : x.inter e = x)
    (h2 : e.inter d = VSet.empty) : x.inter d = VSet.empty :=
  inter_empty_of_mem fun _ hx => mem_inter_empty h2 (mem_of_inter_eq h1 hx)

private theorem sub_or_cancel {x a b : VSet n}
    (h1 : x.inter (a.union b) = x) (h2 : x.inter b = VSet.empty) : x.inter a = x :=
  inter_eq_of_mem fun i hi => by
    have hor := mem_of_inter_eq h1 hi
    rw [VSet.mem_union, mem_inter_empty h2 hi, Bool.or_false] at hor
    exact hor

/-! # The certificate invariant survives one refinement step -/

theorem certInv_refineStep {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hok : StOk n level st)
    (hinj : LabInj st.lab n) (hstarts : StartsOk level st)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hmem : st.active.mem split1 = true) (hs1 : split1 < n)
    (hinv : CertInv ctx level st) :
    CertInv ctx level (refineStep ctx level split1 st) := by
  have hps := hok.ptnSize
  have hls := hok.labSize
  have hend := hok.ptnEnd
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hps] at h
    exact h
  have hrok : StOk n level (refineStep ctx level split1 st) :=
    refineStep_stOk hok
  have hRI : RefInv level st.lab st.ptn
      (refineStep ctx level split1 st) :=
    refInv_refineStep ⟨rfl, rfl, fun _ h => h, cellsPerm_refl _ _ _⟩
      (Nat.le_of_eq hps.symm) (hls.trans hps.symm) hend
  obtain ⟨r, hr⟩ : ∃ r, refineStep ctx level split1 st = r := ⟨_, rfl⟩
  rw [hr] at hrok hRI
  have hcc := refineStep_cell_const (st := st) hok hsymm hs1
  obtain ⟨_, _, hact3⟩ :=
    refineStep_state (st := st) hok hmem
  rw [hr] at hcc hact3
  rw [hr]
  have hgrow := hRI.grow
  have hperm := hRI.perm
  have hrps := hrok.ptnSize
  have hrend := hrok.ptnEnd
  have hrendn : r.ptn[n - 1]! ≤ level := by
    have h := hrend
    rw [hrps] at h
    exact h
  have hrinj : LabInj r.lab n :=
    labInj_of_perm
      (cellsPerm_segN_perm hperm (Nat.le_of_eq hps.symm) hend
        hendn).symm hinj
  have hIsCellOld := cells_isCell (ptn := st.ptn) (level := level)
    (Nat.le_of_eq hps.symm) hend
  have hcbd := cells_end_lt_of_end (ptn := st.ptn) (level := level)
    (Nat.le_of_eq hps.symm) hend hendn
  have hIsCellNew := cells_isCell (ptn := r.ptn) (level := level)
    (Nat.le_of_eq hrps.symm) hrend
  have hrcbd := cells_end_lt_of_end (ptn := r.ptn) (level := level)
    (Nat.le_of_eq hrps.symm) hrend hrendn
  have hdisjOld : ∀ p ∈ cells st.ptn level n,
      ∀ q ∈ cells st.ptn level n, p ≠ q →
      (worksetOf n st.lab p.1 p.2).inter (worksetOf n st.lab q.1 q.2) = VSet.empty :=
    fun p hp q hq hne =>
      worksetOf_cells_disjoint (st := st) hinj hps hend hp hq hne
  have hdisjNew : ∀ p ∈ cells r.ptn level n,
      ∀ q ∈ cells r.ptn level n, p ≠ q →
      (worksetOf n r.lab p.1 p.2).inter (worksetOf n r.lab q.1 q.2) = VSet.empty :=
    fun p hp q hq hne =>
      worksetOf_cells_disjoint (st := r) hrinj hrps hrend hp hq hne
  have hstartuniq : ∀ p ∈ cells st.ptn level n,
      ∀ q ∈ cells st.ptn level n, p.1 = q.1 → p = q := by
    intro p hp q hq he
    rcases pairwise_rel_of_mem cells_pairwise p hp q hq with
      h | h | h
    · exact h
    · have := cells_le p hp
      omega
    · have := cells_le q hq
      omega
  have hstartuniqR : ∀ p ∈ cells r.ptn level n,
      ∀ q ∈ cells r.ptn level n, p.1 = q.1 → p = q := by
    intro p hp q hq he
    rcases pairwise_rel_of_mem cells_pairwise p hp q hq with
      h | h | h
    · exact h
    · have := cells_le p hp
      omega
    · have := cells_le q hq
      omega
  have hws : ∀ D ∈ cells st.ptn level n,
      worksetOf n r.lab D.1 D.2 = worksetOf n st.lab D.1 D.2 := by
    intro D hD
    exact (worksetOf_congr_perm (hperm D.1 (D.2 + 1 - D.1)
      (hIsCellOld D hD))).symm
  obtain ⟨S, hSm, hS1le, hS2ge⟩ := cells_cover (ptn := st.ptn)
    (level := level) (nn := n) split1 hs1
  have hS1 : S.1 = split1 := by
    rcases Nat.eq_or_lt_of_le hS1le with he | hlt
    · exact he
    · exfalso
      have hint := (hIsCellOld S hSm).2.2.1 (split1 - 1) (by omega)
        (by
          have := cells_le S hSm
          omega)
      rcases hstarts split1 hmem with h0 | hbd
      · omega
      · omega
  have hsplit2 : cellEnd st.ptn level split1 = S.2 := by
    rw [cellEnd]
    refine cellEnd_go_unique _ split1 S.2 (by omega)
      (fun i h1 h2 => (hIsCellOld S hSm).2.2.1 i (by omega) (by
        have := cells_le S hSm
        omega)) ?_ (by
        have := hcbd S hSm
        omega)
    have h := (hIsCellOld S hSm).2.2.2
    rw [show S.1 + (S.2 + 1 - S.1) - 1 = S.2 from by
      have := cells_le S hSm
      omega] at h
    exact h
  have hccS : ∀ a len, IsCell r.ptn level a len → a + len ≤ n →
      ConstOn ctx (worksetOf n st.lab S.1 S.2) (segN r.lab a len) := by
    intro a len h1 h2
    have := hcc a len h1 h2
    rw [hsplit2, ← hS1] at this
    exact this
  have hparent : ∀ f ∈ cells r.ptn level n,
      ∃ D ∈ cells st.ptn level n, D.1 ≤ f.1 ∧ f.2 ≤ D.2 := by
    intro f hf
    have hfle := cells_le f hf
    have hfbd := hrcbd f hf
    obtain ⟨c, lenC, hcC, hcle', hcge⟩ := subcell_of_grow
      (ptn0 := st.ptn) (ptnP := r.ptn) (by omega)
      (hIsCellNew f hf) hend hgrow (by omega) (by omega)
    obtain ⟨D, hD, hD1, hD2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) f.1 (by omega)
    rcases isCell_disj_or_eq (hIsCellOld D hD) hcC with
      ⟨he1, he2⟩ | hor | hor
    · refine ⟨D, hD, by omega, ?_⟩
      have hDle := cells_le D hD
      omega
    · exfalso
      have hDle := cells_le D hD
      omega
    · exfalso
      omega
  have hstartfact : ∀ f ∈ cells r.ptn level n,
      ∀ D ∈ cells st.ptn level n, D.1 ≤ f.1 →
        (f.1 = D.1 ∨ r.ptn[f.1 - 1]! ≤ level) := by
    intro f hf D hD hD1
    rcases (hIsCellNew f hf).2.1 with h0 | hbd
    · exact Or.inl (by omega)
    · exact Or.inr hbd
  have hmemW : ∀ (D : Nat × Nat) (pos : Nat) (v : Nat), pos < n → D.1 ≤ pos →
      pos ≤ D.2 → r.lab[pos]! = v →
      (worksetOf n r.lab D.1 D.2).mem v = true := by
    intro D pos v hpos h1 h2 hv
    refine mem_worksetOf_iff.mpr ⟨?_, mem_segN_iff.mpr ⟨pos - D.1, by omega,
      by rw [show D.1 + (pos - D.1) = pos from by omega]; exact hv⟩⟩
    rw [← hv]
    exact hrok.labOk pos (by rw [hrok.labSize]; exact hpos)
  have hcoverB : ∀ D ∈ cells st.ptn level n,
      (st.active.mem D.1 = false ∨ D.1 = split1) →
      ∀ p' ∈ cells r.ptn level n, r.active.mem p'.1 = false →
        D.1 ≤ p'.1 → p'.2 ≤ D.2 →
      ∀ v, (worksetOf n r.lab D.1 D.2).mem v = true →
        (worksetOf n r.lab p'.1 p'.2).mem v = false →
        (activeUnion level r).mem v = true := by
    intro D hD hcase p' hp' hpin hDp1 hDp2 v hv hvp
    obtain ⟨w, hw⟩ := (hact3 D hD).2 hcase
    have hp'le := cells_le p' hp'
    have hp'w : p'.1 = w := by
      rcases Decidable.em (p'.1 = w) with h | h
      · exact h
      · exfalso
        have := hw p'.1 hDp1 (by omega)
          (hstartfact p' hp' D hD hDp1) h
        rw [hpin] at this
        cases this
    obtain ⟨o, ho, hvo⟩ := mem_segN_iff.mp (mem_worksetOf_iff.mp hv).2
    have hDle := cells_le D hD
    have hDbd := hcbd D hD
    obtain ⟨f, hf, hf1, hf2⟩ := cells_cover (ptn := r.ptn)
      (level := level) (nn := n) (D.1 + o) (by omega)
    obtain ⟨E, hE, hE1, hE2⟩ := hparent f hf
    have hED : E = D := by
      rcases isCell_disj_or_eq (hIsCellOld E hE) (hIsCellOld D hD)
        with ⟨he1, _⟩ | hor | hor
      · exact hstartuniq E hE D hD he1
      · exfalso
        have := cells_le E hE
        omega
      · exfalso
        have := cells_le E hE
        omega
    rw [hED] at hE1 hE2
    rcases Decidable.em (f = p') with rfl | hfp
    · exfalso
      have := hmemW f (D.1 + o) v (by omega) hf1 hf2 hvo
      rw [hvp] at this
      cases this
    · have hfw : f.1 ≠ w := by
        intro he
        exact hfp (hstartuniqR f hf p' hp' (by omega))
      have hfact : r.active.mem f.1 = true := by
        refine hw f.1 (by omega) (by
          have := cells_le f hf
          omega) ?_ hfw
        rcases hstartfact f hf D hD hE1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      exact mem_activeUnion.mpr ⟨f, hf, hfact,
        hmemW f (D.1 + o) v (by omega) hf1 hf2 hvo⟩
  have hcoverA : ∀ A ∈ cells st.ptn level n,
      st.active.mem A.1 = true → A.1 ≠ split1 →
      (worksetOf n r.lab A.1 A.2).inter (activeUnion level r) =
        worksetOf n r.lab A.1 A.2 := by
    intro A hA hact hne
    refine inter_eq_of_mem fun v hv => ?_
    obtain ⟨o, ho, hvo⟩ := mem_segN_iff.mp (mem_worksetOf_iff.mp hv).2
    have hAle := cells_le A hA
    have hAbd := hcbd A hA
    obtain ⟨f, hf, hf1, hf2⟩ := cells_cover (ptn := r.ptn)
      (level := level) (nn := n) (A.1 + o) (by omega)
    obtain ⟨E, hE, hE1, hE2⟩ := hparent f hf
    have hED : E = A := by
      rcases isCell_disj_or_eq (hIsCellOld E hE) (hIsCellOld A hA)
        with ⟨he1, _⟩ | hor | hor
      · exact hstartuniq E hE A hA he1
      · exfalso
        have := cells_le E hE
        omega
      · exfalso
        have := cells_le E hE
        omega
    rw [hED] at hE1 hE2
    have hfact : r.active.mem f.1 = true := by
      refine (hact3 A hA).1 hact hne f.1 (by omega) (by
        have := cells_le f hf
        omega) ?_
      rcases hstartfact f hf A hA hE1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    exact mem_activeUnion.mpr ⟨f, hf, hfact,
      hmemW f (A.1 + o) v (by omega) hf1 hf2 hvo⟩
  have htrans : ∀ C ∈ cells st.ptn level n,
      ∀ c' ∈ cells r.ptn level n, C.1 ≤ c'.1 → c'.2 ≤ C.2 →
      ∀ x ∈ segN r.lab c'.1 (c'.2 + 1 - c'.1),
        x ∈ segN st.lab C.1 (C.2 + 1 - C.1) := by
    intro C hC c' hc' h1 h2 x hx
    obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hx
    refine (hperm C.1 (C.2 + 1 - C.1)
      (hIsCellOld C hC)).mem_iff.mpr ?_
    exact mem_segN_iff.mpr ⟨c'.1 - C.1 + o, by
      have := cells_le c' hc'
      omega, by
      rw [show C.1 + (c'.1 - C.1 + o) = c'.1 + o from by omega]⟩
  intro p' hp' hpin c' hc'
  obtain ⟨Dp, hDpm, hDp1, hDp2⟩ := hparent p' hp'
  obtain ⟨C, hCm, hC1, hC2⟩ := hparent c' hc'
  have hp'le := cells_le p' hp'
  have hc'le := cells_le c' hc'
  have hc'bd := hrcbd c' hc'
  have hccC : ConstOn ctx (worksetOf n st.lab S.1 S.2)
      (segN r.lab c'.1 (c'.2 + 1 - c'.1)) :=
    hccS c'.1 (c'.2 + 1 - c'.1) (hIsCellNew c' hc') (by omega)
  rcases Decidable.em (Dp.1 = split1) with hDS | hDS
  · -- the parent is the splitter's cell
    have hDpS : Dp = S := hstartuniq Dp hDpm S hSm (by omega)
    have hsub : (worksetOf n r.lab p'.1 p'.2).inter
        (worksetOf n r.lab Dp.1 Dp.2) = worksetOf n r.lab p'.1 p'.2 :=
      worksetOf_nested hDp1 hDp2 (by omega)
    refine ⟨(worksetOf n r.lab Dp.1 Dp.2).xor (worksetOf n r.lab p'.1 p'.2),
      ?_, ?_, ?_⟩
    · refine inter_eq_of_mem fun v hv => ?_
      have hvD := mem_of_inter_eq (xor_submask hsub) hv
      have hvp : (worksetOf n r.lab p'.1 p'.2).mem v = false :=
        mem_inter_empty (xor_and_self hsub) hv
      exact hcoverB Dp hDpm (Or.inr hDS) p' hp' hpin hDp1 hDp2 v
        hvD hvp
    · intro f hf
      obtain ⟨E, hE, hE1, hE2⟩ := hparent f hf
      rcases Decidable.em (f = p') with rfl | hfp
      · refine Or.inl ?_
        rw [VSet.inter_comm]
        exact xor_and_self hsub
      · rcases Decidable.em (E = Dp) with rfl | hED
        · refine Or.inr ?_
          exact submask_xor_of (worksetOf_nested hE1 hE2 (by
              have := cells_le f hf
              omega))
            (hdisjNew f hf p' hp' hfp)
        · refine Or.inl ?_
          have h1 : (worksetOf n r.lab f.1 f.2).inter
              (worksetOf n r.lab E.1 E.2) = worksetOf n r.lab f.1 f.2 :=
            worksetOf_nested hE1 hE2 (by
              have := cells_le f hf
              omega)
          have h2 : (worksetOf n r.lab E.1 E.2).inter
              (worksetOf n r.lab Dp.1 Dp.2) = VSet.empty := by
            rw [hws E hE, hws Dp hDpm]
            exact hdisjOld E hE Dp hDpm (by
              intro he
              exact hED (by rw [he]))
          have h3 : (worksetOf n r.lab f.1 f.2).inter
              (worksetOf n r.lab Dp.1 Dp.2) = VSet.empty :=
            sub_and_zero h1 h2
          exact zero_of_and_submask h3 (xor_submask hsub)
    · have hor : (worksetOf n r.lab p'.1 p'.2).union
          ((worksetOf n r.lab Dp.1 Dp.2).xor (worksetOf n r.lab p'.1 p'.2)) =
          worksetOf n r.lab Dp.1 Dp.2 := sub_or_xor hsub
      rw [hor, hws Dp hDpm, hDpS]
      exact hccC
  · -- the parent is any other cell; it must have been inactive
    have hDpact : st.active.mem Dp.1 = false := by
      rcases hb : st.active.mem Dp.1 with _ | _
      · rfl
      · exfalso
        have := (hact3 Dp hDpm).1 hb hDS p'.1 hDp1 (by omega)
          (hstartfact p' hp' Dp hDpm hDp1)
        rw [hpin] at this
        cases this
    obtain ⟨V, hVau, hSat, hConst⟩ := hinv Dp hDpm hDpact C hCm
    have hWD := hws Dp hDpm
    have hp'sub : (worksetOf n r.lab p'.1 p'.2).inter
        (worksetOf n r.lab Dp.1 Dp.2) = worksetOf n r.lab p'.1 p'.2 :=
      worksetOf_nested hDp1 hDp2 (by omega)
    have hp'subOld : (worksetOf n r.lab p'.1 p'.2).inter
        (worksetOf n st.lab Dp.1 Dp.2) = worksetOf n r.lab p'.1 p'.2 := by
      rw [← hWD]
      exact hp'sub
    have hWDau : (worksetOf n st.lab Dp.1 Dp.2).inter
        (activeUnion level st) = VSet.empty :=
      inactive_and_activeUnion (st := st) hinj hps hend hDpm hDpact
    have hWDV : (worksetOf n st.lab Dp.1 Dp.2).inter (V) = VSet.empty :=
      zero_of_and_submask hWDau hVau
    have hSDp : S ≠ Dp := by
      intro he
      rw [he] at hS1
      exact hDS hS1
    have hDpS : Dp ≠ S := fun he => hSDp he.symm
    obtain ⟨V0, hV0V, hV0S, hV0deco⟩ : ∃ V0,
        (V0.inter (V) = V0) ∧
        (V0.inter (worksetOf n st.lab S.1 S.2) = VSet.empty) ∧
        (V = V0 ∨ V0.union (worksetOf n st.lab S.1 S.2) = V) := by
      rcases hSat S hSm with h0 | hsub2
      · exact ⟨V, inter_eq_of_mem fun _ h => h, by
          rw [VSet.inter_comm]
          exact h0, Or.inl rfl⟩
      · refine ⟨V.xor (worksetOf n st.lab S.1 S.2), xor_submask hsub2,
          xor_and_self hsub2, Or.inr ?_⟩
        rw [VSet.union_comm]
        exact sub_or_xor hsub2
    have hp'V0 : (worksetOf n r.lab p'.1 p'.2).inter (V0) = VSet.empty :=
      zero_of_and_submask (sub_and_zero hp'subOld hWDV) hV0V
    refine ⟨((worksetOf n r.lab Dp.1 Dp.2).xor (worksetOf n r.lab p'.1 p'.2)).union (V0), ?_, ?_, ?_⟩
    · refine or_submask_of ?_ ?_
      · refine inter_eq_of_mem fun v hv => ?_
        have hvD := mem_of_inter_eq (xor_submask hp'sub) hv
        have hvp : (worksetOf n r.lab p'.1 p'.2).mem v = false :=
          mem_inter_empty (xor_and_self hp'sub) hv
        exact hcoverB Dp hDpm (Or.inl hDpact) p' hp' hpin hDp1 hDp2 v
          hvD hvp
      · refine inter_eq_of_mem fun v hv => ?_
        have hvau : (activeUnion level st).mem v = true :=
          mem_of_inter_eq hVau (mem_of_inter_eq hV0V hv)
        obtain ⟨A, hA, hAact, hAv⟩ := mem_activeUnion.mp hvau
        rcases Decidable.em (A.1 = split1) with he | hne
        · exfalso
          have hAS : A = S := hstartuniq A hA S hSm (by omega)
          rw [hAS] at hAv
          have := mem_inter_empty hV0S hv
          rw [hAv] at this
          cases this
        · refine mem_of_inter_eq (hcoverA A hA hAact hne) ?_
          rw [hws A hA]
          exact hAv
    · intro f hf
      obtain ⟨E, hE, hE1, hE2⟩ := hparent f hf
      have hfle := cells_le f hf
      rcases Decidable.em (f = p') with rfl | hfp
      · refine Or.inl ?_
        refine and_or_zero ?_ hp'V0
        rw [VSet.inter_comm]
        exact xor_and_self hp'sub
      · rcases Decidable.em (E = Dp) with rfl | hEDp
        · refine Or.inr ?_
          exact submask_or_left (submask_xor_of
            (worksetOf_nested hE1 hE2 (by omega))
            (hdisjNew f hf p' hp' hfp))
        · have hfE : (worksetOf n r.lab f.1 f.2).inter
              (worksetOf n st.lab E.1 E.2) = worksetOf n r.lab f.1 f.2 := by
            rw [← hws E hE]
            exact worksetOf_nested hE1 hE2 (by omega)
          have hfXP : (worksetOf n r.lab f.1 f.2).inter
              ((worksetOf n r.lab Dp.1 Dp.2).xor
                (worksetOf n r.lab p'.1 p'.2)) = VSet.empty := by
            refine zero_of_and_submask ?_ (xor_submask hp'sub)
            rw [hWD]
            exact sub_and_zero hfE (hdisjOld E hE Dp hDpm hEDp)
          rcases Decidable.em (E = S) with rfl | hES
          · refine Or.inl ?_
            refine and_or_zero hfXP ?_
            refine sub_and_zero hfE ?_
            rw [VSet.inter_comm]
            exact hV0S
          · rcases hSat E hE with h0 | hsub2
            · refine Or.inl ?_
              refine and_or_zero hfXP ?_
              exact zero_of_and_submask (sub_and_zero hfE h0) hV0V
            · refine Or.inr ?_
              have hEV0 : (worksetOf n st.lab E.1 E.2).inter (V0) =
                  worksetOf n st.lab E.1 E.2 := by
                rcases hV0deco with hdec | hdec
                · rw [← hdec]
                  exact hsub2
                · refine sub_or_cancel (a := V0)
                    (b := worksetOf n st.lab S.1 S.2) ?_ ?_
                  · rw [hdec]
                    exact hsub2
                  · exact hdisjOld E hE S hSm hES
              exact submask_or (submask_trans hfE hEV0)
    · have hConstC' : ConstOn ctx ((worksetOf n st.lab Dp.1 Dp.2).union (V))
          (segN r.lab c'.1 (c'.2 + 1 - c'.1)) :=
        hConst.mono (htrans C hCm c' hc' hC1 hC2)
      have hgoal : ConstOn ctx ((worksetOf n st.lab Dp.1 Dp.2).union (V0))
          (segN r.lab c'.1 (c'.2 + 1 - c'.1)) := by
        rcases hV0deco with hdec | hdec
        · rw [← hdec]
          exact hConstC'
        · have hd : ((worksetOf n st.lab Dp.1 Dp.2).union (V0)).inter
              (worksetOf n st.lab S.1 S.2) = VSet.empty := by
            rw [VSet.inter_comm]
            refine and_or_zero ?_ ?_
            · rw [VSet.inter_comm]
              exact hdisjOld Dp hDpm S hSm hDpS
            · rw [VSet.inter_comm]
              exact hV0S
          refine ConstOn.of_or hd ?_ hccC
          have hre : ((worksetOf n st.lab Dp.1 Dp.2).union V0).union
              (worksetOf n st.lab S.1 S.2) =
              (worksetOf n st.lab Dp.1 Dp.2).union (V) := by
            rw [VSet.union_assoc, hdec]
          rw [hre]
          exact hConstC'
      have hor : (worksetOf n r.lab p'.1 p'.2).union
          (((worksetOf n r.lab Dp.1 Dp.2).xor
            (worksetOf n r.lab p'.1 p'.2)).union V0) =
          (worksetOf n st.lab Dp.1 Dp.2).union V0 := by
        rw [← VSet.union_assoc, sub_or_xor hp'sub, hWD]
      rw [hor]
      exact hgoal

/-! # The fixpoint: refine's output is equitable -/

private theorem labInj_refineStep {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hok : StOk n level st)
    (hinj : LabInj st.lab n) :
    LabInj (refineStep ctx level split1 st).lab n := by
  have hps := hok.ptnSize
  have hend := hok.ptnEnd
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hps] at h
    exact h
  have hRI : RefInv level st.lab st.ptn
      (refineStep ctx level split1 st) :=
    refInv_refineStep ⟨rfl, rfl, fun _ h => h, cellsPerm_refl _ _ _⟩
      (Nat.le_of_eq hps.symm) (hok.labSize.trans hps.symm) hend
  exact labInj_of_perm
    (cellsPerm_segN_perm hRI.perm (Nat.le_of_eq hps.symm) hend
      hendn).symm hinj

/-- The refinement loop leaves the invariants intact and, given fuel
above the potential, exits only discrete or with an exhausted active
set. -/
theorem refineLoop_certInv {ctx : Ctx n} {level : Nat}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u) :
    ∀ (fuel : Nat) (st : RefineSt n), StOk n level st →
      LabInj st.lab n → StartsOk level st →
      CertInv ctx level st →
      st.active.card + 2 * n ≤ fuel + 2 * st.numcells →
      CertInv ctx level (refineLoop ctx level fuel st) ∧
      (¬ (refineLoop ctx level fuel st).numcells < n ∨
        (refineLoop ctx level fuel st).active = VSet.empty)
  | 0, st, hok, hinj, hstarts, hinv, hpot => by
    rw [refineLoop]
    refine ⟨hinv, Or.inl ?_⟩
    have := VSet.card_le st.active
    omega
  | fuel + 1, st, hok, hinj, hstarts, hinv, hpot => by
    rw [refineLoop]
    rcases Decidable.em (st.numcells < n) with hlt | hlt
    · rw [ite_eq_left hlt]
      rcases hps : pickSplit st.active st.hint with _ | split1
      · exact ⟨hinv, Or.inr (active_eq_empty_of_pickSplit_none hps)⟩
      · have hmem := pickSplit_mem hps
        have hs1 : split1 < n :=
          pickSplit_lt hps
        obtain ⟨hp1, hp2, _⟩ :=
          refineStep_state (ctx := ctx) (st := st) hok hmem
        exact refineLoop_certInv hsymm fuel
          (refineStep ctx level split1 st)
          (refineStep_stOk hok)
          (labInj_refineStep hok hinj)
          (refineStep_starts hok hstarts)
          (certInv_refineStep hok hinj hstarts hsymm hmem hs1 hinv)
          (by omega)
    · rw [ite_eq_right hlt]
      exact ⟨hinv, Or.inl hlt⟩

/-- `refine`'s output partition is equitable: entering with a
labelling that is injective on the vertex range, an active set of
cell starts, an accurate cell count, and the certificate invariant
(vacuous when every cell is active), the refinement loop can only
exit discrete or with the active set exhausted, and either way the
final partition is equitable. -/
theorem refine_equitable {ctx : Ctx n} {level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells : Nat}
    (hls : lab.size = n) (hlab : LabOk lab n)
    (hps : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : LabInj lab n)
    (hstarts : ∀ v : Nat, active.mem v = true →
      v = 0 ∨ ptn[v - 1]! ≤ level)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hacc : bcount ptn level n = numcells)
    (hinv : CertInv ctx level
      { lab := lab, ptn := ptn, active := active,
        numcells := numcells, hint := 0, maxpos := 0,
        longcode := numcells }) :
    Equitable ctx level
      (refine ctx level lab ptn active numcells).lab
      (refine ctx level lab ptn active numcells).ptn := by
  rw [refine]
  obtain ⟨st0, hst0⟩ : ∃ st0 : RefineSt n,
      RefineSt.mk lab ptn active numcells 0 0 numcells = st0 :=
    ⟨_, rfl⟩
  have hok0 : StOk n level st0 := by
    rw [← hst0]
    exact ⟨hls, hlab, hps, by
      show ptn[ptn.size - 1]! ≤ level
      exact hend⟩
  have hinj0 : LabInj st0.lab n := by
    rw [← hst0]
    exact hinj
  have hstarts0 : StartsOk level st0 := by
    rw [← hst0]
    exact hstarts
  have hinv0 : CertInv ctx level st0 := by
    rw [← hst0]
    exact hinv
  have hpot : st0.active.card + 2 * n ≤
      (4 * n + 8) + 2 * st0.numcells := by
    have := VSet.card_le st0.active
    omega
  obtain ⟨hinvR, hexit⟩ := refineLoop_certInv hsymm (4 * n + 8)
    st0 hok0 hinj0 hstarts0 hinv0 hpot
  have hfrz : FreezeInv level n ptn numcells
      (refineLoop ctx level (4 * n + 8) st0) := by
    refine freezeInv_refineLoop hps.symm hend (4 * n + 8) st0 ?_
    rw [← hst0]
    refine ⟨rfl, ?_, fun _ _ => rfl, rfl⟩
    show lab.size = ptn.size
    rw [hls, hps]
  rw [hst0]
  obtain ⟨rl, hrl⟩ : ∃ rl : RefineSt n,
      refineLoop ctx level (4 * n + 8) st0 = rl := ⟨_, rfl⟩
  rw [hrl] at hinvR hexit hfrz
  rw [hrl]
  show Equitable ctx level rl.lab rl.ptn
  rcases hexit with hnc | hact
  · -- discrete exit: the accurate count forces singleton cells
    have hcount := hfrz.count
    rw [hacc] at hcount
    have hbc : n ≤ bcount rl.ptn level n := by omega
    have hall : ∀ q, q < n → rl.ptn[q]! ≤ level := by
      have hle := bcount_le rl.ptn level n
      rw [bcount] at hbc
      have hlen := List.countP_eq_length
        (p := fun q => decide (rl.ptn[q]! ≤ level))
        (l := List.range n)
      have : (List.range n).countP
          (fun q => decide (rl.ptn[q]! ≤ level)) =
          (List.range n).length := by
        rw [List.length_range]
        have := List.countP_le_length
          (p := fun q => decide (rl.ptn[q]! ≤ level))
          (l := List.range n)
        rw [List.length_range] at this
        omega
      intro q hq
      have := (hlen.mp this) q (List.mem_range.mpr hq)
      simpa using this
    refine equitable_of_singletons fun cd hcd => ?_
    have hic := cells_isCell (ptn := rl.ptn) (level := level)
      (nn := n) (by
        rw [hfrz.ptnSize, hps]
        exact Nat.le_refl _) (by
        have h1 := hfrz.frozen (ptn.size - 1) hend
        rw [hfrz.ptnSize]
        rw [h1]
        exact hend) cd hcd
    have hle := cells_le cd hcd
    have hbd := cells_end_lt_of_end (ptn := rl.ptn) (level := level)
      (by
        rw [hfrz.ptnSize, hps]
        exact Nat.le_refl _) (by
        have h1 := hfrz.frozen (ptn.size - 1) hend
        rw [hfrz.ptnSize]
        rw [h1]
        exact hend) (by
        have h1 := hfrz.frozen (ptn.size - 1) hend
        rw [show ptn.size - 1 = n - 1 from by rw [hps]] at h1
        rw [h1]
        exact (by rw [← hps]; exact hend)) cd hcd
    rcases Nat.eq_or_lt_of_le hle with he | hlt2
    · exact he.symm
    · exfalso
      have hint := hic.2.2.1 cd.1 (Nat.le_refl _) (by omega)
      have := hall cd.1 (by omega)
      omega
  · exact equitable_of_certInv_exit hinvR hact

end Hex.GraphIso.Nauty


