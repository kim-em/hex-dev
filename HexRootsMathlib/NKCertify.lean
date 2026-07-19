/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Loop
public import HexRootsMathlib.NKWitness

public section

/-!
# Soundness of NK-only component certification

This module follows both executable `.nk` certification paths: the doubled
enclosing square and the coverage-guarded speculative Newton square.
-/

namespace HexRootsMathlib

noncomputable section

/-- An NK-only certification result is either the coverage-guarded speculative
candidate or the doubled enclosing base square. -/
theorem certify_nk_cases {p : Hex.ZPoly} {c : Hex.Component}
    {r : Hex.Certified p} (hcert : Hex.Component.certify? p .nk c = some r) :
    let base := (Hex.encSquare c.squares).doubled
    let cand := (Hex.newtonSquare p base 1).doubled
    (∃ (_hbase : Hex.nkWitness p base) (_hinside : cand.squareInside base = true)
        (hcand : Hex.nkWitness p cand),
        r = .atom ⟨cand, Or.inl hcand⟩) ∨
      ∃ hbase : Hex.nkWitness p base,
        r = .atom ⟨base, Or.inl hbase⟩ := by
  simp only [Hex.Component.certify?, Hex.nkWitness] at hcert ⊢
  split at hcert <;> rename_i hbase
  · split at hcert <;> rename_i hinside
    · split at hcert <;> rename_i hcand
      · left
        exact ⟨hbase, hinside, hcand, Option.some.inj hcert.symm⟩
      · right
        exact ⟨hbase, Option.some.inj hcert.symm⟩
    · right
      exact ⟨hbase, Option.some.inj hcert.symm⟩
  · simp at hcert

/-- The semantic region of an explicitly NK-certified atom is its closed
square. -/
@[simp] theorem nkAtom_region {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (h : Hex.nkWitness p s) :
    Certified.region (.atom ⟨s, Or.inl h⟩) = DyadicSquare.closedSquare s := by
  simp [Certified.region, DyadicRootIsolation.region, h]

/-- A root in an outer unique-root square belongs to a nested inner square
that also has a unique root. -/
theorem nkRoot_mem_nested {p : Hex.ZPoly} {inner outer : Hex.DyadicSquare}
    (hinner : Hex.nkWitness p inner) (houter : Hex.nkWitness p outer)
    (hsubset : DyadicSquare.closedSquare inner ⊆
      DyadicSquare.closedSquare outer) {z : ℂ}
    (hzroot : (toPolyℂ p).eval z = 0)
    (hzouter : z ∈ DyadicSquare.closedSquare outer) :
    z ∈ DyadicSquare.closedSquare inner := by
  obtain ⟨zi, hzi, -⟩ := NKData.existsUnique_root hinner
  obtain ⟨zo, hzo, hunique⟩ := NKData.existsUnique_root houter
  have hz_eq : z = zo := hunique z ⟨hzroot, hzouter⟩
  have hzi_eq : zi = zo := hunique zi ⟨hzi.1, hsubset hzi.2⟩
  rw [hz_eq, ← hzi_eq]
  exact hzi.2

/-- Every NK-only certification result is an atom carrying an executable NK
witness and hence exactly one root in its stored closed square. -/
theorem certify_nk_unique {p : Hex.ZPoly} {c : Hex.Component}
    {r : Hex.Certified p} (hcert : Hex.Component.certify? p .nk c = some r) :
    ∃ (iso : Hex.DyadicRootIsolation p), r = .atom iso ∧
      Hex.nkWitness p iso.square ∧
      ∃! z, (toPolyℂ p).eval z = 0 ∧
        z ∈ DyadicSquare.closedSquare iso.square := by
  rcases certify_nk_cases hcert with h | h
  · obtain ⟨hbase, hinside, hcand, rfl⟩ := h
    exact ⟨_, rfl, hcand, NKData.existsUnique_root hcand⟩
  · obtain ⟨hbase, rfl⟩ := h
    exact ⟨_, rfl, hbase, NKData.existsUnique_root hbase⟩

/-- Every NK-only certification result contains a unique interior simple root
in its stored square. -/
theorem certify_nk_sound {p : Hex.ZPoly} {c : Hex.Component}
    {r : Hex.Certified p} (hcert : Hex.Component.certify? p .nk c = some r) :
    ∃ (iso : Hex.DyadicRootIsolation p), r = .atom iso ∧
      ∃ z, (toPolyℂ p).eval z = 0 ∧
        z ∈ DyadicSquare.openSquare iso.square ∧
        (toPolyℂ p).derivative.eval z ≠ 0 ∧
        ∀ w, (toPolyℂ p).eval w = 0 →
          w ∈ DyadicSquare.closedSquare iso.square → w = z := by
  rcases certify_nk_cases hcert with h | h
  · obtain ⟨hbase, hinside, hcand, rfl⟩ := h
    exact ⟨_, rfl, NKData.sound hcand⟩
  · obtain ⟨hbase, rfl⟩ := h
    exact ⟨_, rfl, NKData.sound hbase⟩

/-- NK-only component certification preserves every input-component root,
including through the speculative recentring branch. -/
theorem certifier_preserves_nk (p : Hex.ZPoly) : Certifier.Preserves p .nk := by
  intro c r hcert z hzroot hz
  rcases certify_nk_cases hcert with h | h
  · obtain ⟨hbase, hinside, hcand, rfl⟩ := h
    rw [nkAtom_region hcand]
    apply nkRoot_mem_nested hcand hbase
      (DyadicSquare.closedSquare_subset_of_squareInside hinside) hzroot
    exact Component.region_subset_doubledEnc c hz
  · obtain ⟨hbase, rfl⟩ := h
    rw [nkAtom_region hbase]
    exact Component.region_subset_doubledEnc c hz

/-- Successful NK-only loop execution preserves all polynomial roots covered
by its starting worklist. -/
theorem isolateLoop_nk_covers {p : Hex.ZPoly} {target : Int} {fuel : Nat}
    {work : Array Hex.Component} {rs : Array (Hex.Certified p)}
    (hloop : Hex.isolateLoop p target .nk fuel work = some rs)
    {z : ℂ} (hzroot : (toPolyℂ p).IsRoot z)
    (hz : z ∈ Worklist.region work) : z ∈ Results.region rs :=
  isolateLoop_covers (certifier_preserves_nk p) hloop hzroot hz

end

end HexRootsMathlib
