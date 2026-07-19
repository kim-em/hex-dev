/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Isolate

public section

/-!
# Semantic preservation by refinement

Both public refinement APIs preserve the unique complex root selected by the
input atom whenever they return successfully.
-/

open Complex Polynomial Set

namespace HexRootsMathlib

noncomputable section

namespace DyadicRootIsolation

/-- Refining an atom certificate preserves its selected complex root. -/
theorem refineTo_root {p : Hex.ZPoly} (iso : Hex.DyadicRootIsolation p)
    (target : Int) (strategy : Hex.AtomStrategy)
    {iso' : Hex.DyadicRootIsolation p}
    (hrun : iso.refineTo? target strategy = some iso') :
    root iso' = root iso := by
  by_cases hready : target ≤ iso.square.prec
  · simp only [Hex.DyadicRootIsolation.refineTo?, if_pos hready,
      Option.some.injEq] at hrun
    subst iso'
    rfl
  · rw [Hex.DyadicRootIsolation.refineTo?, if_neg hready] at hrun
    let fuel := Hex.fuelFor p target iso.square.prec
    let work : Array Hex.Component := #[⟨#[iso.square.doubled], 1⟩]
    cases hloop : Hex.isolateLoop p target strategy fuel work with
    | none => simp [fuel, work, hloop] at hrun
    | some rs =>
        have hrun' := hrun
        simp only [fuel, work, hloop] at hrun'
        by_cases hsize : rs.size = 1
        · simp only [hsize, ↓reduceIte] at hrun'
          cases hget : rs[0]? with
          | none => simp [hget] at hrun'
          | some r =>
              cases hr : r with
              | atom out =>
                  rw [hget, hr] at hrun'
                  have hout : out = iso' := Option.some.inj hrun'
                  subst out
                  have hzregion : root iso ∈ region iso :=
                    openRegion_subset_region iso (root_spec iso).2.1
                  have hzwork : root iso ∈ Worklist.region work := by
                    refine ⟨⟨#[iso.square.doubled], 1⟩, ?_, ?_⟩
                    · simp [work]
                    · simpa [Component.region, Hex.Certified.square] using
                        (Certified.region_subset_toComponent (.atom iso) hzregion)
                  have hzresults : root iso ∈ Results.region rs :=
                    isolateLoop_covers (certifier_preserves p strategy) hloop
                      (isRoot iso) hzwork
                  obtain ⟨r', hr'mem, hzr'⟩ := hzresults
                  have hzero : 0 < rs.size := by omega
                  have hget0 : rs[0] = .atom iso' := by
                    rw [Array.getElem?_eq_getElem hzero] at hget
                    exact (Option.some.inj hget).trans hr
                  have hr'eq : r' = .atom iso' := by
                    obtain ⟨i, hiList, hir⟩ := List.getElem_of_mem hr'mem
                    have hi : i < rs.size := by simpa using hiList
                    have hi0 : i = 0 := by omega
                    subst i
                    have hr'zero : r' = rs[0] := by
                      rw [← hir]
                      exact Array.getElem_toList hi
                    rw [hr'zero, hget0]
                  rw [hr'eq] at hzr'
                  exact ((root_spec iso').2.2.2 (root iso)
                    (isRoot iso) hzr').symm
              | cluster cl => simp [hget, hr] at hrun'
        · simp [hsize] at hrun'

end DyadicRootIsolation

namespace RefinedIsolation

/-- Refined-level refinement preserves the semantic root represented by the
returned subtype. This operational result is unconditional: it follows from
the successful raw refinement call, independently of quotient semantics. -/
theorem refineTo_root {p : Hex.ZPoly} (r : Hex.RefinedIsolation p)
    (target : Int) (strategy : Hex.AtomStrategy)
    {out : {r' : Hex.RefinedIsolation p //
      Hex.SimpleRoot.mk r' = Hex.SimpleRoot.mk r}}
    (hrun : r.refineTo? target strategy = some out) :
    root out.1 = root r := by
  rw [Hex.RefinedIsolation.refineTo?] at hrun
  cases hraw : r.1.refineTo? (max target (Hex.mahlerPrec p : Int)) strategy with
  | none => simp [hraw] at hrun
  | some iso' =>
      simp only [Option.bind_eq_bind, hraw, Option.bind_some] at hrun
      split at hrun
      · rename_i hprec
        split at hrun
        · have hout := Option.some.inj hrun
          subst out
          exact DyadicRootIsolation.refineTo_root r.1
            (max target (Hex.mahlerPrec p : Int)) strategy hraw
        · contradiction
      · contradiction

end RefinedIsolation

end

end HexRootsMathlib
