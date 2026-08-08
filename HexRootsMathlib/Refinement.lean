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
  rw [Hex.DyadicRootIsolation.refineTo?] at hrun
  split at hrun
  · have hiso : iso = iso' := Option.some.inj hrun
    subst iso'
    rfl
  · cases hfast : Hex.refineFastAtom? iso target strategy with
    | some tau =>
        have htau : tau = iso' := by
          simpa only [hfast, Option.some.injEq] using hrun
        subst tau
        have hzregion : root iso ∈ Certified.region (.atom iso) :=
          openRegion_subset_region iso (root_spec iso).2.1
        have hzout : root iso ∈ Certified.region (.atom iso') :=
          refineFastAtom_preserves (certifier_preserves p strategy) hfast
            (isRoot iso) hzregion
        exact ((root_spec iso').2.2.2 (root iso) (isRoot iso) hzout).symm
    | none =>
        have hzregion : root iso ∈ Certified.region (.atom iso) :=
          openRegion_subset_region iso (root_spec iso).2.1
        have hzout : root iso ∈ Certified.region (.atom iso') :=
          refineAtom_preserves (certifier_preserves p strategy)
            (by simpa only [hfast] using hrun) (isRoot iso) hzregion
        exact ((root_spec iso').2.2.2 (root iso) (isRoot iso) hzout).symm

/-- Every successful raw refinement result reaches its requested precision. -/
theorem refineTo_ready {p : Hex.ZPoly} {iso iso' : Hex.DyadicRootIsolation p}
    {target : Int} {strategy : Hex.AtomStrategy}
    (hrun : iso.refineTo? target strategy = some iso') :
    target ≤ iso'.square.prec := by
  rw [Hex.DyadicRootIsolation.refineTo?] at hrun
  split at hrun
  · rename_i hready
    have hiso : iso = iso' := Option.some.inj hrun
    subst iso'
    exact hready
  · cases hfast : Hex.refineFastAtom? iso target strategy with
    | some tau =>
        have htau : tau = iso' := by
          simpa only [hfast, Option.some.injEq] using hrun
        subst tau
        exact refineFastAtom_ready hfast
    | none =>
        exact refineAtom_ready (by simpa only [hfast] using hrun)

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
