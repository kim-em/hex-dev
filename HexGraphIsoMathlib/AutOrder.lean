/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIsoMathlib.AutOrbits
public import HexGraphIso.AutIndiv
public import Mathlib.Data.Fintype.EquivFin
import all HexGraphIso.Autos
import all HexGraphIso.Iso

public section

namespace Hex.GraphIso.Aut

variable {n k : Nat} {G : Colored n k}

/-- A non-singleton orbit supplies another vertex in the selected colour
cell, so the checked individualization succeeds. -/
theorem indiv_of_orbitSize (v : Fin n) (h : 1 < orbitSize G v) :
    ∃ H, indiv? G v = some H := by
  classical
  let _ := Fintype.ofFinite (MulAction.orbit (group G) v)
  rw [orbitSize_card, Nat.card_eq_fintype_card] at h
  obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card h
    (⟨v, MulAction.mem_orbit_self v⟩ : MulAction.orbit (group G) v)
  have hw : w.val ≠ v := fun he => hne (Subtype.ext he)
  obtain ⟨p, hp, hv⟩ := ((mem_orbit G v w.val).mp w.property).elim
  apply indiv_exists w.val hw
  simpa only [← Hex.Vector.get_eq_getElem, hv] using hp.1 v

/-- The individualized graph's full automorphism group is the point
stabilizer in the original full group. -/
def indivEquiv {v : Fin n} {H : Colored n (k + 1)} (h : indiv? G v = some H) :
    MulAction.stabilizer (group G) v ≃ group H where
  toFun p := ⟨p.val.val, (indiv_isIso h _).mpr ⟨p.val.property, p.property⟩⟩
  invFun p := ⟨⟨p.val, ((indiv_isIso h _).mp p.property).1⟩, ((indiv_isIso h _).mp p.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Orbit-stabilizer for the exact individualization used by `orderAux`. -/
theorem indiv_card {v : Fin n} {H : Colored n (k + 1)} (h : indiv? G v = some H) :
    Nat.card (group G) = orbitSize G v * Nat.card (group H) := by
  rw [orbitSize_card, ← Nat.card_congr (indivEquiv h),
    ← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (group G) v)]

private theorem card_of_fixed (h : ∀ p, IsIso G G p → ∀ v, p.get v = v) :
    Nat.card (group G) = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨1, fun p => Subtype.ext (Perm.ext fun v => ?_)⟩
  simpa only [OneMemClass.coe_one, Perm.one_get] using h p.val p.property v

private theorem card_of_singletons (h : ∀ v : Fin n, orbitSize G v ≤ 1) :
    Nat.card (group G) = 1 := by
  classical
  apply card_of_fixed
  intro p hp v
  let _ := Fintype.ofFinite (MulAction.orbit (group G) v)
  have hc := h v
  rw [orbitSize_card, Nat.card_eq_fintype_card] at hc
  have hs := Fintype.card_le_one_iff_subsingleton.mp hc
  exact congrArg Subtype.val (hs.elim
    (⟨p.get v, (mem_orbit G v _).mpr (SameOrbit.intro p hp rfl)⟩ : MulAction.orbit (group G) v)
    ⟨v, MulAction.mem_orbit_self v⟩)

private theorem card_of_colors (h : n ≤ k) : Nat.card (group G) = 1 := by
  have hk : k ≤ n := by simpa using Fintype.card_le_of_surjective _ G.coloring.onto
  have he : n = k := by omega
  have hi := G.coloring.onto.injective_of_finite (finCongr he)
  apply card_of_fixed
  intro p hp v
  exact hi (hp.1 v)

/-- One unit of fuel per remaining possible colour suffices for the
existing orbit-stabilizer recursion. No additional search bookkeeping is
needed: every successful recursive step adds a colour. -/
theorem orderAux_card (fuel : Nat) :
    ∀ {k : Nat} (G : Colored n k), n ≤ k + fuel →
      orderAux fuel G (orbits G) = Nat.card (group G) := by
  classical
  induction fuel with
  | zero =>
    intro k G hk
    rw [orderAux]
    exact (card_of_colors (by omega)).symm
  | succ fuel ih =>
    intro k G hk
    rw [orderAux]
    cases hf : (List.finRange n).find? (fun v => decide (1 < sizeAt (orbits G) n v.val)) with
    | none =>
      have hall : ∀ v : Fin n, orbitSize G v ≤ 1 := by
        intro v
        have h := List.find?_eq_none.mp hf v (List.mem_finRange v)
        simpa only [decide_eq_true_eq, Nat.not_lt, orbitSize] using h
      exact (card_of_singletons hall).symm
    | some v =>
      have hv : 1 < orbitSize G v := by
        simpa only [decide_eq_true_eq, orbitSize] using List.find?_some hf
      obtain ⟨H, hH⟩ := indiv_of_orbitSize v hv
      dsimp only
      rw [hH]
      dsimp only
      rw [ih H (by omega), indiv_card hH]
      rfl

/-- The reported order is the cardinality of the full colour-preserving
automorphism group. -/
theorem order_card (G : Colored n k) : order G = Nat.card (group G) :=
  orderAux_card n G (by omega)

end Hex.GraphIso.Aut
