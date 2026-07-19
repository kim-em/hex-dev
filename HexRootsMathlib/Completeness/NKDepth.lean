/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.NKConverse
public import HexRootsMathlib.HasOnlySimpleRoots
public import HexRootsMathlib.MahlerPrec
public import HexRootsMathlib.NKCertify

public section

/-!
# Newton certification at the executable separation depth

This module instantiates the root-product converse with the explicit depth
chosen by `Hex.separationDepth`.  Its logarithmic degree term makes the total
contribution of all remote roots uniformly small.
-/

open Polynomial

namespace HexRootsMathlib.NKData

noncomputable section

/-- A convenient elementary upper bound for a small binomial tail. -/
theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hnsmall : (n : ℝ) * x ≤ 1 / 2 := by
        apply le_trans _ hsmall
        gcongr
        norm_num
      have hind := ih hnsmall
      rw [pow_succ]
      calc
        (1 + x) ^ n * (1 + x) ≤ (1 + 2 * n * x) * (1 + x) := by
          gcongr
        _ ≤ 1 + 2 * (n + 1) * x := by
          have hxsmall : 2 * n * x ≤ 1 := by nlinarith
          nlinarith
        _ = 1 + 2 * (↑(n + 1) : ℝ) * x := by push_cast; ring

/-- The numerical tail threshold used by `witness_of_remote_roots`. -/
theorem one_add_pow_sub_one_le {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 96) :
    (1 + x) ^ n - 1 ≤ 1 / 32 := by
  have hhalf : (n : ℝ) * x ≤ 1 / 2 := hsmall.trans (by norm_num)
  have hpow := one_add_pow_le hx n hhalf
  nlinarith

/-- At `separationDepth`, the executable upper radius times the degree is at
most one 256th of the Mahler-radius scale. -/
theorem radiusHi_mul_degree_le {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec) :
    Dyadic.toReal s.radiusHi * (Nat.max 2 (p.degree?.getD 0) : ℝ) ≤
      ((2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)) / 256 := by
  let n := Nat.max 2 (p.degree?.getD 0)
  let L := Hex.ceilLog2 n
  let m := Hex.mahlerPrec p
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ L := by
    exact_mod_cast le_two_pow_ceilLog2 n
  have hpow : (2 : ℝ) ^ (-s.prec) ≤
      (2 : ℝ) ^ (-(m + L + 8 : Nat) : ℤ) := by
    apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    dsimp [m, L, n]
    rw [Hex.separationDepth, Hex.sepSlack] at hprec
    omega
  rw [DyadicSquare.radiusHi_eq, DyadicSquare.halfWidth_eq]
  rw [show Dyadic.toReal Hex.sqrt2Hi = (1449 / 1024 : ℝ) by
    norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]]
  change (2 : ℝ) ^ (-s.prec) * (1449 / 1024 : ℝ) * (n : ℝ) ≤ _
  calc
    _ ≤ (2 : ℝ) ^ (-(m + L + 8 : Nat) : ℤ) *
        (1449 / 1024 : ℝ) * (2 : ℝ) ^ L := by gcongr
    _ = ((2 : ℝ) ^ (-(m + L + 8 : Nat) : ℤ) * (2 : ℝ) ^ (L : ℤ)) *
        (1449 / 1024 : ℝ) := by rw [zpow_natCast]; ring
    _ = (2 : ℝ) ^ ((-(m + L + 8 : Nat) : ℤ) + (L : ℤ)) *
        (1449 / 1024 : ℝ) := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ (-(m : ℤ) - 8) * (1449 / 1024 : ℝ) := by
      congr 2
      push_cast
      ring
    _ = ((2 : ℝ) ^ (-(m : ℤ)) * (1449 / 1024 : ℝ)) / 256 := by
      rw [show -(m : ℤ) - 8 = -(m : ℤ) + (-8 : ℤ) by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
      ring
    _ = _ := rfl

/-- A root lying in the central half of a square at the executable separation
depth satisfies the actual Newton--Kantorovich witness. -/
theorem witness_at_separationDepth {p : Hex.ZPoly} {s : Hex.DyadicSquare}
    {z : ℂ} (hsize : 1 < p.size)
    (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hz : (toPolyℂ p).IsRoot z)
    (hprec : (Hex.separationDepth p : Int) ≤ s.prec)
    (hcenter : HexRootsMathlib.supNorm (z - DyadicSquare.center s) ≤
      DyadicSquare.halfWidth s / 2) :
    Hex.nkWitness p s := by
  let f := toPolyℂ p
  let c := DyadicSquare.center s
  let rho := Dyadic.toReal s.radiusHi
  let N := Nat.max 2 (p.degree?.getD 0)
  let M := (2 : ℝ) ^ (-(Hex.mahlerPrec p : ℤ)) * (1449 / 1024 : ℝ)
  let d := 3 * M
  have hf : f ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun q : Polynomial ℂ => q.coeff (p.size - 1)) hzero
    dsimp [f] at hcoeff
    rw [coeff_toPolyℂ] at hcoeff
    apply Hex.DensePoly.coeff_last_ne_zero_of_pos_size p (by omega)
    exact_mod_cast hcoeff
  have hsepC : f.Separable := by
    have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := RingHom.ext_int _ _
    rw [show f = (HexPolyZMathlib.toPolyℚ p).map (algebraMap ℚ ℂ) by
      dsimp [f, HexPolyZMathlib.toPolyℚ]
      rw [Polynomial.map_map, hcomp]]
    exact hsep.map
  have hzmem : z ∈ f.roots := (mem_roots hf).2 hz
  obtain ⟨roots, hroots⟩ := Multiset.exists_cons_of_mem hzmem
  have hrootsEq : f.roots = z ::ₘ roots := hroots
  have hnodup : f.roots.Nodup := nodup_roots hsepC
  have hne : ∀ w ∈ roots, w ≠ z := by
    intro w hw heq
    subst w
    rw [hrootsEq] at hnodup
    exact (Multiset.nodup_cons.mp hnodup).1 hw
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hrho : 0 < rho := by
    dsimp [rho]
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt2Hi : 0 < Dyadic.toReal Hex.sqrt2Hi := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    exact mul_pos (by rw [DyadicSquare.halfWidth_eq]; positivity) hsqrt2Hi
  have hrhoN : rho * N ≤ M / 256 := by
    simpa [rho, N, M] using radiusHi_mul_degree_le hprec
  have hN : 2 ≤ N := by exact Nat.le_max_left _ _
  have hrhoM : rho ≤ M / 512 := by
    have htwo : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [mul_le_mul_of_nonneg_left htwo hrho.le]
  have hzc : ‖z - c‖ ≤ rho / 2 := by
    have hnorm : ‖z - c‖ ≤ √2 * HexRootsMathlib.supNorm (z - c) :=
      Complex.norm_le_sqrt_two_mul_max (z - c)
    have hsqrt : √2 * DyadicSquare.halfWidth s < rho := by
      dsimp [rho]
      simpa only [DyadicSquare.radius, mul_comm] using
        DyadicSquare.radius_lt_radiusHi s
    calc
      ‖z - c‖ ≤ √2 * (DyadicSquare.halfWidth s / 2) :=
        hnorm.trans (mul_le_mul_of_nonneg_left hcenter (Real.sqrt_nonneg 2))
      _ = (√2 * DyadicSquare.halfWidth s) / 2 := by ring
      _ ≤ rho / 2 := by linarith
  have hremote : ∀ w ∈ roots, d ≤ ‖w - c‖ := by
    intro w hw
    have hsepzw := mahlerPrec_separates p hsep z w hz
      ((mem_roots hf).1 (hrootsEq ▸ Multiset.mem_cons_of_mem hw)) (hne w hw).symm
    change M < ‖z - w‖ / 4 at hsepzw
    rw [norm_sub_rev] at hsepzw
    have htri : ‖w - z‖ ≤ ‖w - c‖ + ‖z - c‖ := by
      calc
        ‖w - z‖ = ‖(w - c) - (z - c)‖ := by ring_nf
        _ ≤ ‖w - c‖ + ‖z - c‖ := norm_sub_le _ _
    dsimp [d]
    nlinarith
  have hcard : roots.card + 1 = p.degree?.getD 0 := by
    calc
      roots.card + 1 = f.roots.card := by rw [hrootsEq]; simp
      _ = f.natDegree := (IsAlgClosed.splits f).natDegree_eq_card_roots.symm
      _ = p.degree?.getD 0 := by simpa [f] using natDegree_toPolyℂ p
  have hcardN : roots.card ≤ N := by
    have hcdeg : roots.card ≤ p.degree?.getD 0 := by omega
    exact hcdeg.trans (Nat.le_max_right _ _)
  have hprod : (roots.card : ℝ) * rho ≤ M / 256 := by
    calc
      (roots.card : ℝ) * rho ≤ (N : ℝ) * rho := by
        gcongr
      _ = rho * N := by ring
      _ ≤ M / 256 := hrhoN
  have hsmall : (roots.card : ℝ) * ((4 * rho) / d) ≤ 1 / 96 := by
    rw [show (roots.card : ℝ) * ((4 * rho) / d) =
      ((roots.card : ℝ) * (4 * rho)) / (3 * M) by dsimp [d]; ring]
    apply (div_le_iff₀ (by positivity : 0 < 3 * M)).2
    nlinarith
  apply witness_of_remote_roots hf hsize hrootsEq hd hremote hcenter
  dsimp [rho, d]
  apply one_add_pow_sub_one_le
  · positivity
  · simpa [rho, d] using hsmall

/-- Once the doubled enclosing square has an NK witness, the executable
NK-only certifier returns either its guarded speculative candidate or the
base atom. -/
theorem certify_nk_exists_of_witness {p : Hex.ZPoly} {c : Hex.Component}
    (hbase : Hex.nkWitness p (Hex.encSquare c.squares).doubled) :
    ∃ r, Hex.Component.certify? p .nk c = some r := by
  simp only [Hex.Component.certify?, Hex.nkWitness] at hbase ⊢
  split
  · split
    · split
      · simp
      · simp
    · simp
  · rename_i hnot
    exact (hnot hbase).elim

/-- A component root in the central half of its doubled enclosing square
forces the actual `.nk` certification path at `separationDepth`.  The depth
hypothesis is deliberately on that enclosing square: deriving it from the
component's leaf precision requires the separate gluing-width invariant. -/
theorem component_certify_nk {p : Hex.ZPoly} {c : Hex.Component} {z : ℂ}
    (hsize : 1 < p.size) (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hz : (toPolyℂ p).IsRoot z) (hzc : z ∈ Component.region c)
    (hprec : (Hex.separationDepth p : Int) ≤
      (Hex.encSquare c.squares).doubled.prec) :
    ∃ r, Hex.Component.certify? p .nk c = some r := by
  let enc := Hex.encSquare c.squares
  let base := enc.doubled
  have hzenc : z ∈ DyadicSquare.closedSquare enc :=
    Component.region_subset_encSquare c hzc
  have hzsup : HexRootsMathlib.supDist z (DyadicSquare.center enc) ≤
      DyadicSquare.halfWidth enc := by
    simpa [DyadicSquare.closedSquare, supClosedBall] using hzenc
  have hcenter : HexRootsMathlib.supNorm (z - DyadicSquare.center base) ≤
      DyadicSquare.halfWidth base / 2 := by
    change HexRootsMathlib.supDist z (DyadicSquare.center base) ≤
      DyadicSquare.halfWidth base / 2
    rw [show DyadicSquare.center base = DyadicSquare.center enc by rfl,
      show DyadicSquare.halfWidth base = 2 * DyadicSquare.halfWidth enc by
        exact DyadicSquare.doubled_halfWidth enc]
    nlinarith
  have hbase : Hex.nkWitness p base :=
    witness_at_separationDepth hsize hsep hz (by simpa [base] using hprec) hcenter
  exact certify_nk_exists_of_witness (by simpa [base, enc] using hbase)

/-- The successful fixed-depth NK certificate continues to cover the
designated component root, including through speculative recentring. -/
theorem component_certify_nk_covers {p : Hex.ZPoly} {c : Hex.Component} {z : ℂ}
    (hsize : 1 < p.size) (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
    (hz : (toPolyℂ p).IsRoot z) (hzc : z ∈ Component.region c)
    (hprec : (Hex.separationDepth p : Int) ≤
      (Hex.encSquare c.squares).doubled.prec) :
    ∃ r, Hex.Component.certify? p .nk c = some r ∧ z ∈ Certified.region r := by
  obtain ⟨r, hr⟩ := component_certify_nk hsize hsep hz hzc hprec
  exact ⟨r, hr, certifier_preserves_nk p c r hr z hz hzc⟩

end

end HexRootsMathlib.NKData
