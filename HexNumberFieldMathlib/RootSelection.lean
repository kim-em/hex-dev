/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.RootSelection
public import HexNumberFieldMathlib.Interval
public import HexNumberFieldMathlib.Conjugate
public section

/-! Lazy selection certifies a maximum without constructing real coordinates. -/
namespace Hex.AlgebraicRoot

/-- Lazy half-plane classification agrees with the selected complex value. -/
theorem side_value (a : AlgebraicRoot) :
    a.side = if a.toComplex.im = 0 then .real
      else if 0 < a.toComplex.im then .upper else .lower :=
  AlgebraicNumber.sideOf_root a.rep

/-- The lower tag is exactly the negative imaginary half plane. -/
theorem side_nonneg (a : AlgebraicRoot) : a.side ≠ .lower ↔ 0 ≤ a.toComplex.im := by
  rw [side_value]
  by_cases h : a.toComplex.im = 0
  · simp [h]
  · by_cases hp : 0 < a.toComplex.im
    · simp [h, hp, hp.le]
    · have hn : a.toComplex.im < 0 := lt_of_le_of_ne (le_of_not_gt hp) h
      simp [h, hp, not_le_of_gt hn]

end Hex.AlgebraicRoot

namespace Hex.RootSelection
open HexRootsMathlib

private theorem same_reps {p q : ZPoly} (hp : p = q)
    (a : RefinedIsolation p) (b : RefinedIsolation q)
    (h : (hp ▸ a).sameRoot b = true) : a.root = b.root := by
  cases hp
  exact (RefinedIsolation.intersects_iff_root_eq a b).mp h

/-- A successful same-polynomial test identifies the selected complex value. -/
theorem same_sound (a b : AlgebraicRoot) (h : same a b = true) :
    a.toComplex = b.toComplex := by
  unfold same at h
  split at h
  · rename_i hp
    exact same_reps hp a.rep b.rep h
  · contradiction

private theorem pick_eq (a b : Work) : pick a b = a ∨ pick a b = b := by
  unfold pick
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private theorem fold_mem (roots : List Work) (a : Work) :
    roots.foldl pick a ∈ a :: roots := by
  induction roots generalizing a with
  | nil => simp
  | cons b rest ih =>
    have hm := ih (pick a b)
    rcases List.mem_cons.mp hm with h | h
    · rcases pick_eq a b with hp | hp
      · exact List.mem_cons.mpr (Or.inl (h.trans hp))
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl (h.trans hp))))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- Every accepted domination check is an inequality of actual real coordinates. -/
theorem dominates_sound (a b : Work) (h : dominates a b = true) :
    b.root.toComplex.re ≤ a.root.toComplex.re := by
  simp only [dominates, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with he | hi
  · rw [same_sound a.root b.root he]
  · have hc := Interval.realOrder?_sound b.root.rep a.root.rep hi
    exact (compare_lt_iff_lt.mp hc).le

/-- A validated proposal is an input and dominates every input. -/
theorem probe_spec (roots : List Work) {a : Work} (h : probe roots = some a) :
    a ∈ roots ∧ ∀ b ∈ roots, b.root.toComplex.re ≤ a.root.toComplex.re := by
  cases roots with
  | nil => simp [probe] at h
  | cons b rest =>
    simp only [probe] at h
    split at h
    · rename_i hall
      have he := Option.some.inj h
      subst a
      refine ⟨fold_mem rest b, ?_⟩
      intro c hc
      exact dominates_sound _ c (List.all_eq_true.mp hall c hc)
    · contradiction

/-- Refinement updates only the enclosure of a lazy value. -/
theorem refine?_value (bits : Nat) (a : Work) {b : Work} (h : refine? bits a = some b) :
    b.root.toComplex = a.root.toComplex := by
  unfold refine? at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have he := Option.some.inj h
  subst b
  exact RefinedIsolation.refineTo_root a.root.rep _ .nkThenPellet hr

/-- Refining an array preserves its entire ordered value list. -/
theorem refine_list (bits : Nat) (roots : List Work) {out : List Work}
    (h : roots.mapM (refine? bits) = some out) :
    out.map (fun a => a.root.toComplex) = roots.map (fun a => a.root.toComplex) := by
  induction roots generalizing out with
  | nil => simpa using h.symm
  | cons a rest ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
    have he := Option.some.inj h
    subst out
    simp only [List.map_cons, refine?_value bits a hb, ih ht]

/-- Every successful bounded search certifies membership and maximal real coordinate. -/
theorem search_spec (rounds : List Nat) (roots : List Work) {a : AlgebraicRoot}
    (h : search rounds roots = some a) :
    a.toComplex ∈ roots.map (fun r => r.root.toComplex) ∧
      ∀ z ∈ roots.map (fun r => r.root.toComplex), z.re ≤ a.toComplex.re := by
  induction rounds generalizing roots with
  | nil =>
    unfold search at h
    cases hp : probe roots with
    | none => simp [hp] at h
    | some best =>
      have he : best.root = a := by simpa [hp] using h
      subst a
      obtain ⟨hm, hd⟩ := probe_spec roots hp
      refine ⟨List.mem_map.mpr ⟨best, hm, rfl⟩, ?_⟩
      rintro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact hd b hb
  | cons bits rest ih =>
    rw [search] at h
    cases hp : probe roots with
    | some best =>
      have he : best.root = a := by simpa [hp] using h
      subst a
      obtain ⟨hm, hd⟩ := probe_spec roots hp
      refine ⟨List.mem_map.mpr ⟨best, hm, rfl⟩, ?_⟩
      rintro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact hd b hb
    | none =>
      simp only [hp] at h
      obtain ⟨out, hout, h⟩ := Option.bind_eq_some_iff.mp h
      have hi := ih out h
      rwa [refine_list bits roots hout] at hi

/-- Public lazy selection is sound independently of the refinement budget. -/
theorem select?_spec (roots : List AlgebraicRoot) {a : AlgebraicRoot}
    (h : select? roots = some a) :
    a.toComplex ∈ roots.map AlgebraicRoot.toComplex ∧
      ∀ z ∈ roots.map AlgebraicRoot.toComplex, z.re ≤ a.toComplex.re := by
  simpa only [List.map_map, Function.comp_def] using search_spec [16, 64] _ h

end Hex.RootSelection

namespace Hex.AlgebraicNumber.Radical

/-- Imaginary-side ranking detects the nonnegative half plane. -/
theorem rank_nonneg (a : AlgebraicNumber) :
    0 ≤ rank a ↔ 0 ≤ a.toComplex.im := by
  have h := a.isolation.sign
  change match a.side with
    | .real => a.toComplex.im = 0
    | .upper => 0 < a.toComplex.im
    | .lower => a.toComplex.im < 0 at h
  unfold rank
  cases hs : a.side <;> simp_all <;> linarith

private theorem twiceRe_value (a : Candidate) :
    a.twiceRe.toComplex = ((2 * a.value.toComplex.re : ℝ) : ℂ) := by
  rw [a.correct, add_toComplex, conj_toComplex, Complex.add_conj]

private theorem compare_value (a b : Candidate) :
    realCompare a.twiceRe b.twiceRe =
      compare (2 * a.value.toComplex.re) (2 * b.value.toComplex.re) := by
  rw [realCompare_eq _ _ ((isReal_iff _).mpr (by rw [twiceRe_value]; rfl))
    ((isReal_iff _).mpr (by rw [twiceRe_value]; rfl)), twiceRe_value, twiceRe_value]
  rfl

/-- Lexicographic dominance by real coordinate and imaginary side. -/
@[expose] def Dominates (a b : Candidate) : Prop :=
  b.value.toComplex.re ≤ a.value.toComplex.re ∧
    (b.value.toComplex.re = a.value.toComplex.re → rank b.value ≤ rank a.value)

private theorem dominates_refl (a : Candidate) : Dominates a a := ⟨le_rfl, fun _ => le_rfl⟩

private theorem dominates_trans {a b c : Candidate}
    (hab : Dominates a b) (hbc : Dominates b c) : Dominates a c := by
  refine ⟨hbc.1.trans hab.1, fun h => ?_⟩
  have hb : b.value.toComplex.re = a.value.toComplex.re := by linarith [hab.1, hbc.1]
  exact (hbc.2 (h.trans hb.symm)).trans (hab.2 hb)

private theorem choose_spec (a b : Candidate) :
    (choose a b = a ∨ choose a b = b) ∧
      Dominates (choose a b) a ∧ Dominates (choose a b) b := by
  have hc := compare_value a b
  unfold choose
  cases h : realCompare a.twiceRe b.twiceRe with
  | lt =>
    have hr := compare_lt_iff_lt.mp (h.symm.trans hc).symm
    exact ⟨Or.inr rfl, ⟨by linarith, fun he => by linarith⟩, dominates_refl b⟩
  | gt =>
    have hr := compare_gt_iff_gt.mp (h.symm.trans hc).symm
    exact ⟨Or.inl rfl, dominates_refl a, ⟨by linarith, fun he => by linarith⟩⟩
  | eq =>
    have hr := compare_eq_iff_eq.mp (h.symm.trans hc).symm
    simp only
    split
    · rename_i hk
      exact ⟨Or.inr rfl, ⟨by linarith, fun _ => hk.le⟩, dominates_refl b⟩
    · rename_i hk
      exact ⟨Or.inl rfl, dominates_refl a, ⟨by linarith, fun _ => le_of_not_gt hk⟩⟩

private theorem fold_spec (rs : List RootCount) (a : Candidate) :
    let b := rs.foldl (fun best root => choose best (candidate root)) a
    (b = a ∨ ∃ r ∈ rs, b = candidate r) ∧
      Dominates b a ∧ ∀ r ∈ rs, Dominates b (candidate r) := by
  induction rs generalizing a with
  | nil => exact ⟨Or.inl rfl, dominates_refl a, by simp⟩
  | cons r rs ih =>
    obtain ⟨hm, ha, hall⟩ := ih (choose a (candidate r))
    obtain ⟨hc, hca, hcr⟩ := choose_spec a (candidate r)
    refine ⟨?_, dominates_trans ha hca, ?_⟩
    · rcases hm with hm | ⟨s, hs, hm⟩
      · rcases hc with hc | hc
        · exact Or.inl (hm.trans hc)
        · exact Or.inr ⟨r, by simp, hm.trans hc⟩
      · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, hm⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact dominates_trans ha hcr
      · exact hall s hs

/-- The exact reference selector returns an input dominating every input. -/
theorem select_spec (roots : Array RootCount) (hne : roots.toList ≠ []) :
    ∃ c, select roots = some c ∧ (∃ r ∈ roots.toList, c = candidate r) ∧
      ∀ r ∈ roots.toList, Dominates c (candidate r) := by
  unfold select
  cases h : roots.toList with
  | nil => exact (hne h).elim
  | cons r rs =>
    obtain ⟨hm, ha, hall⟩ := fold_spec rs (candidate r)
    refine ⟨_, rfl, ?_, ?_⟩
    · rcases hm with hm | ⟨s, hs, hm⟩
      · exact ⟨r, by simp, hm⟩
      · exact ⟨s, List.mem_cons_of_mem _ hs, hm⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ha
      · exact hall s hs


end Hex.AlgebraicNumber.Radical

namespace Hex.RootSelection

/-- The shared maximum selector succeeds on nonempty inputs and preserves its contract
whether the interval path or the exact reference supplies the result. -/
theorem maximum?_spec (roots : List AlgebraicRoot) (hne : roots ≠ []) :
    ∃ a, maximum? roots = some a ∧ a.toComplex ∈ roots.map AlgebraicRoot.toComplex ∧
      ∀ z ∈ roots.map AlgebraicRoot.toComplex, z.re ≤ a.toComplex.re := by
  unfold maximum?
  cases hf : select? roots with
  | some root =>
    have hs := select?_spec roots hf
    refine ⟨root.exact, rfl, ?_⟩
    simpa only [AlgebraicRoot.exact_toComplex] using hs
  | none =>
    let counts := (roots.map fun r => (⟨r, 1, by decide⟩ : RootCount)).toArray
    have hcne : counts.toList ≠ [] := by simpa [counts] using hne
    obtain ⟨c, hc, ⟨r, hr, hcr⟩, hdom⟩ := AlgebraicNumber.Radical.select_spec counts hcne
    refine ⟨c.value, ?_, ?_, ?_⟩
    · rw [hc]
      rfl
    · have hr' : r ∈ roots.map (fun r => (⟨r, 1, by decide⟩ : RootCount)) := by
        simpa only [counts, List.toList_toArray] using hr
      obtain ⟨a, ha, hra⟩ := List.mem_map.mp hr'
      subst r
      rw [hcr]
      simp only [AlgebraicNumber.Radical.candidate]
      rw [AlgebraicRoot.exact_toComplex]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      have hd := hdom (⟨a, 1, by decide⟩ : RootCount)
        (by simpa only [counts, List.toList_toArray] using
          (List.mem_map.mpr ⟨a, ha, rfl⟩ :
            (⟨a, 1, by decide⟩ : RootCount) ∈ roots.map (fun r => ⟨r, 1, by decide⟩)))
      have hdre := hd.1
      simp only [AlgebraicNumber.Radical.candidate] at hdre
      simpa only [AlgebraicRoot.exact_toComplex] using hdre

end Hex.RootSelection
