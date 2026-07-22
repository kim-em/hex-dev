/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexArith.Nat.Prime
public meta import HexBerlekamp.Factor
public meta import HexBerlekamp.Irreducibility
public meta import HexHensel.Basic
public meta import HexHensel.Multifactor
public meta import HexHensel.QuadraticMultifactor
public meta import HexMatrix.Basic
public meta import HexPolyZ.Mignotte
public meta import HexLLL.Basic
public import HexArith.Nat.Prime
public import HexBerlekamp.Factor
public import HexBerlekamp.Irreducibility
public import HexHensel.Multifactor
public import HexHensel.QuadraticMultifactor
public import HexLLL.Basic
-- Needed so `decide`/`rfl` over `DensePoly`/`Array` equality reduces in the
-- kernel: the core `Array.instDecidableEq` delegates its nonempty case to the
-- non-`@[expose]` `Array.instDecidableEqImpl`, which is otherwise opaque under
-- the module system. Drop once that impl is exposed upstream (lean4).
import all Init.Data.Array.DecidableEq

public import HexBerlekampZassenhaus.FactorEntryPoints
public meta import HexBerlekampZassenhaus.FactorEntryPoints
import all HexBerlekampZassenhaus.PrimeSelection
import all HexBerlekampZassenhaus.Records
import all HexBerlekampZassenhaus.Certificate
import all HexBerlekampZassenhaus.ChoosePrimeData
import all HexBerlekampZassenhaus.ReassemblyProofs
import all HexBerlekampZassenhaus.Lattice
import all HexBerlekampZassenhaus.BhksCandidates
import all HexBerlekampZassenhaus.BhksRecover
import all HexBerlekampZassenhaus.Recombination
import all HexBerlekampZassenhaus.FactorEntryPoints

public section
set_option backward.proofsInPublic true

/-!
This module collects the `Irreducible` class, the constant/linear/size-two arms, and the main mod-p theorem.
-/
namespace Hex

/-- Every recorded entry of the default public factorization has positive
leading coefficient. -/
theorem factorize_entry_leadingCoeff_pos
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    0 < DensePoly.leadingCoeff entry.1 := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_leadingCoeff_pos f (factorFactors f) entry hmem

/-- Every recorded entry of the default public factorization passes the
`shouldRecordPolynomialFactor` filter. -/
theorem factorize_entry_shouldRecord
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    shouldRecordPolynomialFactor entry.1 = true := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  have hmem' : entry ∈ (collectFactorMultiplicities (factorFactors f)).toList := by
    simpa only [factorizationOfFactors] using hmem
  exact collectFactorMultiplicities_entry_shouldRecord (factorFactors f) entry hmem'

/-- Any recorded entry of the default public factorization comes from the
hybrid's raw factor array `factorFactors`, up to sign normalization. -/
theorem factorize_entry_mem_raw_source
    (f : ZPoly) (entry : ZPoly × Nat)
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList) :
    ∃ raw ∈ (factorFactors f).toList, entry.1 = normalizeFactorSign raw := by
  rw [factorize_eq_factorizationOfFactors] at hmem
  exact factorizationOfFactors_entry_mem_normalized_raw f (factorFactors f) entry hmem

/-- Every recorded entry of the default public factorization is primitive once
every raw factor in the hybrid's raw factor array is primitive. -/
theorem factorize_entry_primitive_of_chosen_raw_primitive
    {f : ZPoly} {entry : ZPoly × Nat}
    (hmem : entry ∈ (ZPoly.factorize f).factors.toList)
    (h_raw : ∀ raw ∈ (factorFactors f).toList, ZPoly.Primitive raw) :
    ZPoly.Primitive entry.1 := by
  obtain ⟨raw, hraw_mem, hentry_eq⟩ := factorize_entry_mem_raw_source f entry hmem
  rw [hentry_eq]
  exact normalizeFactorSign_primitive _ (h_raw raw hraw_mem)

/-- Public-entry specialisation: every recorded entry is primitive once the
hybrid's raw factor array is primitive entrywise. -/
theorem factorize_entries_primitive
    (f : ZPoly)
    (h_raw : ∀ raw ∈ (factorFactors f).toList, ZPoly.Primitive raw) :
    ∀ entry ∈ (ZPoly.factorize f).factors, ZPoly.Primitive entry.1 := by
  intro entry hentry
  exact factorize_entry_primitive_of_chosen_raw_primitive
    (Array.mem_toList_iff.mpr hentry) h_raw

/-- The default public factorization has no duplicate polynomial keys. -/
theorem factorize_pairwise_first
    (f : ZPoly) :
    List.Pairwise (fun a b : ZPoly × Nat => a.1 ≠ b.1)
      (ZPoly.factorize f).factors.toList := by
  rw [factorize_eq_factorizationOfFactors]
  exact factorizationOfFactors_pairwise_first f (factorFactors f)

private def quadraticSquareRegression : ZPoly :=
  let q : ZPoly := DensePoly.ofCoeffs #[-1, 0, 1]
  q * q

#guard (ZPoly.factorize quadraticSquareRegression).factors =
  #[(linearFactorForRoot (-1), 2), (linearFactorForRoot 1, 2)]

private def quadraticCubeRegression : ZPoly :=
  let q : ZPoly := DensePoly.ofCoeffs #[-1, 0, 1]
  q * q * q

#guard (ZPoly.factorize quadraticCubeRegression).factors =
  #[(linearFactorForRoot (-1), 3), (linearFactorForRoot 1, 3)]

/-- Soundness regression for issue #6799: the primitive non-monic cubic
`2X³+9X²+10X+3 = (2X+1)(X+1)(X+3)` must split into three factors, not be
reported as a single irreducible factor.  Before the `ZPoly.dilate`
inverse-transform fix, the slow exhaustive recombination recombined against the
non-monic core via a scalar `DensePoly.scale`, failed to find any split, and
fell back to `#[core]`. -/
private def nonMonicCubicRegression : ZPoly :=
  DensePoly.ofCoeffs #[3, 10, 9, 2]

#guard (ZPoly.factorize nonMonicCubicRegression).factors.size = 3
#guard Factorization.product (ZPoly.factorize nonMonicCubicRegression) = nonMonicCubicRegression

/-- Non-monic quadratic with two integer roots, `2(X-1)(X+1) = 2X²-2`:
content `2`, primitive part `(X-1)(X+1)`, so `factorize` records two factors. -/
private def nonMonicQuadraticTwoRoots : ZPoly :=
  DensePoly.ofCoeffs #[-2, 0, 2]

#guard (ZPoly.factorize nonMonicQuadraticTwoRoots).factors.size = 2
#guard Factorization.product (ZPoly.factorize nonMonicQuadraticTwoRoots) = nonMonicQuadraticTwoRoots

/-- Non-monic quartic `(2X+1)(X+1)(X²+1)`, primitive with leading coefficient
`2` and a mix of non-monic linear, monic linear, and irreducible quadratic
factors. -/
private def nonMonicQuarticRegression : ZPoly :=
  DensePoly.ofCoeffs #[1, 2] * DensePoly.ofCoeffs #[1, 1] *
    DensePoly.ofCoeffs #[1, 0, 1]

#guard (ZPoly.factorize nonMonicQuarticRegression).factors.size = 3
#guard Factorization.product (ZPoly.factorize nonMonicQuarticRegression) = nonMonicQuarticRegression

/-- Non-monic core carrying nontrivial content, `6(X-1)(X+1) = 6X²-6`: the signed
content scalar is `6` and the primitive factors are the two integer roots. -/
private def nonMonicWithContentRegression : ZPoly :=
  DensePoly.ofCoeffs #[-6, 0, 6]

#guard (ZPoly.factorize nonMonicWithContentRegression).factors.size = 2
#guard Factorization.product (ZPoly.factorize nonMonicWithContentRegression) =
  nonMonicWithContentRegression
#guard (ZPoly.factorize nonMonicWithContentRegression).scalar = 6

namespace ZPoly

/--
Mathlib-free irreducibility predicate for integer polynomials.

The class form lets downstream Mathlib-free APIs request irreducibility through
typeclass inference. The predicate remains the usual nonzero, non-unit, no
proper factorization condition.
-/
class Irreducible (f : ZPoly) : Prop where
  /-- The zero polynomial is not irreducible. -/
  not_zero : f ≠ 0
  /-- Units are excluded from irreducibility. -/
  not_unit : ¬ ZPoly.IsUnit f
  /-- Every product decomposition has a unit factor. -/
  no_factors :
    ∀ a b : ZPoly, f = a * b → ZPoly.IsUnit a ∨ ZPoly.IsUnit b

/-- Mathlib-free associatedness predicate for integer polynomials: `a` and
`b` are associated when `b = a * u` for some `ZPoly`-unit `u` (i.e. `u = ±1`).
Used by HO-1 irreducibility dischargers to translate "Mathlib-side irreducible factor
of the square-free core" to the direct non-divisibility hypothesis required
by the greedy expansion helper. -/
def Associated (a b : ZPoly) : Prop :=
  ∃ u : ZPoly, ZPoly.IsUnit u ∧ b = a * u

def isNatPrime (n : Nat) : Bool :=
  2 ≤ n && !((List.range n).any fun d => 2 ≤ d && d * d ≤ n && n % d == 0)

/--
Computational irreducibility checker backed by the public factorization API.

Constants are checked by integer primality. Positive-degree polynomials are
checked from the returned `Factorization`: the scalar must be a unit and there
must be exactly one polynomial factor with multiplicity one.
-/
@[expose]
def isIrreducible (f : ZPoly) : Bool :=
  if f = 0 then
    false
  else if f.degree?.getD 0 = 0 then
    let k := (f.coeff 0).natAbs
    isNatPrime k
  else
    let φ := ZPoly.factorize f
    decide (φ.scalar.natAbs = 1) &&
      φ.factors.size == 1 &&
      match φ.factors.toList with
      | [entry] => decide (entry.2 = 1)
      | _ => false

/-- A polynomial of dense size `1` is the constant polynomial of its zeroth
coefficient. The trimming invariant on `DensePoly` forces the single stored
coefficient to be nonzero, so `coeff 0` already names the unique stored entry. -/
theorem eq_C_of_size_eq_one (a : ZPoly) (hsize : a.size = 1) :
    a = DensePoly.C (a.coeff 0) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)

/-- An integer factor of `1` is `±1`. Used to read off the unit factor in
size-two monic polynomial irreducibility proofs. -/
private theorem int_factor_one_eq_unit {x y : Int} (h : x * y = 1) :
    x = 1 ∨ x = -1 := by
  have hx_dvd : x ∣ (1 : Int) := ⟨y, h.symm⟩
  have hxnat_dvd : x.natAbs ∣ (1 : Nat) := by
    have := Int.natAbs_dvd_natAbs.mpr hx_dvd
    simpa using this
  have hxnat_le : x.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hxnat_dvd
  have hx_ne : x ≠ 0 := by
    intro hzero
    rw [hzero] at h
    rw [Int.zero_mul] at h
    omega
  have hxnat_pos : 1 ≤ x.natAbs := by
    rcases Nat.eq_zero_or_pos x.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hx_ne
    · exact hpos
  have hxnat_eq : x.natAbs = 1 := by omega
  rcases Int.natAbs_eq x with heq | heq
  · left
    rw [heq, hxnat_eq]
    rfl
  · right
    rw [heq, hxnat_eq]
    rfl

/-- Correctness lemma for `isNatPrime`: the Boolean check reduces to the
elementary characterisation that `n ≥ 2` and no divisor `d` with
`2 ≤ d ≤ √n` divides `n`. -/
private theorem isNatPrime_iff (n : Nat) :
    isNatPrime n = true ↔
      2 ≤ n ∧ ∀ d : Nat, 2 ≤ d → d * d ≤ n → ¬ d ∣ n := by
  unfold isNatPrime
  rw [Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true', List.any_eq_false]
  refine Iff.intro ?fwd ?bwd
  case fwd =>
    rintro ⟨h2, hany⟩
    refine ⟨h2, fun d hd2 hdd_le hdvd => ?_⟩
    have hd_lt_n : d < n := by
      have h2d_le_dd : 2 * d ≤ d * d := Nat.mul_le_mul_right d hd2
      have h2d_le_n : 2 * d ≤ n := Nat.le_trans h2d_le_dd hdd_le
      omega
    have hmem : d ∈ List.range n := List.mem_range.mpr hd_lt_n
    have hpred_ne_true : ¬
        ((decide (2 ≤ d) && decide (d * d ≤ n) && (n % d == 0)) = true) :=
      hany d hmem
    apply hpred_ne_true
    have h1 : (decide (2 ≤ d)) = true := decide_eq_true hd2
    have h2 : (decide (d * d ≤ n)) = true := decide_eq_true hdd_le
    have h3 : (n % d == 0) = true := by
      rw [beq_iff_eq]
      exact Nat.mod_eq_zero_of_dvd hdvd
    rw [h1, h2, h3]
    rfl
  case bwd =>
    rintro ⟨h2, hno⟩
    refine ⟨h2, fun d hmem => ?_⟩
    have hd_lt_n : d < n := List.mem_range.mp hmem
    intro hpred_true
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff, beq_iff_eq] at hpred_true
    obtain ⟨⟨hd2, hdd_le⟩, hmod⟩ := hpred_true
    exact hno d hd2 hdd_le (Nat.dvd_of_mod_eq_zero hmod)

/-- `DensePoly.C` on integers commutes with multiplication: `C (a*b) = C a * C b`.
Used by the constant-polynomial Irreducible characterisation to split integer
factorisations into polynomial factorisations and back. -/
private theorem zpoly_C_mul_C (a b : Int) :
    DensePoly.C (a * b) = (DensePoly.C a : ZPoly) * DensePoly.C b := by
  rw [ZPoly.C_mul_eq_scale]
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_scale (R := Int) a (DensePoly.C b) n (Int.mul_zero a),
      DensePoly.coeff_C, DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn, if_neg hn]
    exact (Int.mul_zero a).symm

/-- Size of `DensePoly.C k` for nonzero `k` is exactly `1`. -/
private theorem zpoly_size_C_of_ne_zero {k : Int} (hk : k ≠ 0) :
    (DensePoly.C k : ZPoly).size = 1 := by
  unfold DensePoly.size
  rw [DensePoly.coeffs_C_of_ne_zero hk]
  rfl

/-- A constant polynomial `DensePoly.C k` is `ZPoly.Irreducible` whenever
`k.natAbs` is prime in the elementary `isNatPrime` sense. -/
theorem irreducible_C_of_isNatPrime
    {k : Int} (hp : isNatPrime k.natAbs = true) :
    ZPoly.Irreducible (DensePoly.C k) := by
  obtain ⟨hp2, hpno⟩ := (isNatPrime_iff k.natAbs).mp hp
  have hk_ne : k ≠ 0 := by
    intro hzero
    rw [hzero] at hp2
    change 2 ≤ (0 : Int).natAbs at hp2
    simp at hp2
  have hk_natAbs_ne_one : k.natAbs ≠ 1 := by omega
  have hC_ne : DensePoly.C k ≠ 0 := by
    intro hzero
    have : (DensePoly.C k).coeff 0 = (DensePoly.C (0 : Int)).coeff 0 := by
      rw [hzero]
      rfl
    rw [DensePoly.coeff_C, DensePoly.coeff_C] at this
    simp at this
    exact hk_ne this
  refine
    { not_zero := hC_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · have hk1 : k = 1 := by
        have hc : (DensePoly.C k).coeff 0 = (DensePoly.C (1 : Int)).coeff 0 :=
          congrArg (fun p => DensePoly.coeff p 0) hone
        rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
        simpa using hc
      apply hk_natAbs_ne_one
      rw [hk1]
      rfl
    · have hkn1 : k = -1 := by
        have hc : (DensePoly.C k).coeff 0 = (DensePoly.C (-1 : Int)).coeff 0 :=
          congrArg (fun p => DensePoly.coeff p 0) hneg
        rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
        simpa using hc
      apply hk_natAbs_ne_one
      rw [hkn1]
      rfl
  · intro a b hab
    by_cases ha_zero : a = 0
    · exfalso
      apply hC_ne
      rw [hab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hC_ne
      rw [hab, hb_zero, DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hC_size : (DensePoly.C k).size = 1 := zpoly_size_C_of_ne_zero hk_ne
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hab] at hab_size
    rw [hC_size] at hab_size
    have ha_one : a.size = 1 := by omega
    have hb_one : b.size = 1 := by omega
    have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
    have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
    have ha_coeff_ne : a.coeff 0 ≠ 0 := by
      intro h
      apply ha_zero
      rw [ha_eq, h]
      rfl
    have hb_coeff_ne : b.coeff 0 ≠ 0 := by
      intro h
      apply hb_zero
      rw [hb_eq, h]
      rfl
    -- (C a₀) * (C b₀) = C (a₀ * b₀) = C k, so a₀ * b₀ = k
    have hprod_C : DensePoly.C (a.coeff 0 * b.coeff 0) = DensePoly.C k := by
      calc DensePoly.C (a.coeff 0 * b.coeff 0)
          = DensePoly.C (a.coeff 0) * DensePoly.C (b.coeff 0) :=
            zpoly_C_mul_C _ _
        _ = a * b := by rw [← ha_eq, ← hb_eq]
        _ = DensePoly.C k := hab.symm
    have hcoeff_prod : a.coeff 0 * b.coeff 0 = k := by
      have hc : (DensePoly.C (a.coeff 0 * b.coeff 0)).coeff 0 =
          (DensePoly.C k).coeff 0 :=
        congrArg (fun p => DensePoly.coeff p 0) hprod_C
      rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
      simpa using hc
    have hnat_prod :
        (a.coeff 0).natAbs * (b.coeff 0).natAbs = k.natAbs := by
      have := Int.natAbs_mul (a.coeff 0) (b.coeff 0)
      rw [hcoeff_prod] at this
      exact this.symm
    by_cases ha_unit : ZPoly.IsUnit a
    · exact Or.inl ha_unit
    by_cases hb_unit : ZPoly.IsUnit b
    · exact Or.inr hb_unit
    exfalso
    have ha_natAbs_pos : 0 < (a.coeff 0).natAbs := by
      rcases Nat.eq_zero_or_pos (a.coeff 0).natAbs with hzero | hpos
      · exact absurd (Int.natAbs_eq_zero.mp hzero) ha_coeff_ne
      · exact hpos
    have hb_natAbs_pos : 0 < (b.coeff 0).natAbs := by
      rcases Nat.eq_zero_or_pos (b.coeff 0).natAbs with hzero | hpos
      · exact absurd (Int.natAbs_eq_zero.mp hzero) hb_coeff_ne
      · exact hpos
    have ha_natAbs_ge_two : 2 ≤ (a.coeff 0).natAbs := by
      have ha_natAbs_ne_one : (a.coeff 0).natAbs ≠ 1 := by
        intro hone
        apply ha_unit
        rcases Int.natAbs_eq (a.coeff 0) with heq | heq
        · left; rw [ha_eq, heq, hone]; rfl
        · right; rw [ha_eq, heq, hone]; rfl
      omega
    have hb_natAbs_ge_two : 2 ≤ (b.coeff 0).natAbs := by
      have hb_natAbs_ne_one : (b.coeff 0).natAbs ≠ 1 := by
        intro hone
        apply hb_unit
        rcases Int.natAbs_eq (b.coeff 0) with heq | heq
        · left; rw [hb_eq, heq, hone]; rfl
        · right; rw [hb_eq, heq, hone]; rfl
      omega
    rcases Nat.le_total (a.coeff 0).natAbs (b.coeff 0).natAbs with hle | hle
    · have hsq_le : (a.coeff 0).natAbs * (a.coeff 0).natAbs ≤ k.natAbs := by
        calc (a.coeff 0).natAbs * (a.coeff 0).natAbs
            ≤ (a.coeff 0).natAbs * (b.coeff 0).natAbs :=
              Nat.mul_le_mul_left _ hle
          _ = k.natAbs := hnat_prod
      have hdvd : (a.coeff 0).natAbs ∣ k.natAbs :=
        ⟨(b.coeff 0).natAbs, hnat_prod.symm⟩
      exact hpno (a.coeff 0).natAbs ha_natAbs_ge_two hsq_le hdvd
    · have hsq_le : (b.coeff 0).natAbs * (b.coeff 0).natAbs ≤ k.natAbs := by
        calc (b.coeff 0).natAbs * (b.coeff 0).natAbs
            ≤ (a.coeff 0).natAbs * (b.coeff 0).natAbs :=
              Nat.mul_le_mul_right _ hle
          _ = k.natAbs := hnat_prod
      have hdvd : (b.coeff 0).natAbs ∣ k.natAbs :=
        ⟨(a.coeff 0).natAbs, by rw [Nat.mul_comm]; exact hnat_prod.symm⟩
      exact hpno (b.coeff 0).natAbs hb_natAbs_ge_two hsq_le hdvd

/-- An irreducible constant polynomial `DensePoly.C k` (for `k ≠ 0`) has
`k.natAbs` prime in the elementary `isNatPrime` sense. -/
theorem isNatPrime_natAbs_of_irreducible_C
    {k : Int} (hk_ne : k ≠ 0) (hirr : ZPoly.Irreducible (DensePoly.C k)) :
    isNatPrime k.natAbs = true := by
  rw [isNatPrime_iff]
  have hk_natAbs_pos : 0 < k.natAbs := by
    rcases Nat.eq_zero_or_pos k.natAbs with hzero | hpos
    · exact absurd (Int.natAbs_eq_zero.mp hzero) hk_ne
    · exact hpos
  have hk_natAbs_ne_one : k.natAbs ≠ 1 := by
    intro hone
    apply hirr.not_unit
    rcases Int.natAbs_eq k with heq | heq
    · left
      rw [heq, hone]
      rfl
    · right
      rw [heq, hone]
      rfl
  have hk_natAbs_ge_two : 2 ≤ k.natAbs := by omega
  refine ⟨hk_natAbs_ge_two, fun d hd2 hdd_le hdvd => ?_⟩
  obtain ⟨e, he⟩ := hdvd
  have he_pos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with hzero | hpos
    · rw [hzero] at he
      simp at he
      omega
    · exact hpos
  have he_ge_two : 2 ≤ e := by
    have h_le : d * d ≤ d * e := by rw [← he]; exact hdd_le
    have hd_pos : 0 < d := by omega
    have hde : d ≤ e := Nat.le_of_mul_le_mul_left h_le hd_pos
    omega
  -- |k| = d * e, so either k = (d : Int) * e or k = -((d : Int) * e).
  rcases Int.natAbs_eq k with heq | heq
  · have hk_eq : k = (d : Int) * (e : Int) := by
      rw [heq, he, Int.natCast_mul]
    have hC_split :
        DensePoly.C k = DensePoly.C (d : Int) * DensePoly.C (e : Int) := by
      rw [hk_eq, zpoly_C_mul_C]
    rcases hirr.no_factors _ _ hC_split with hua | hub
    · rcases hua with hone | hneg
      · have hd_eq : (d : Int) = 1 := by
          have hc : (DensePoly.C (d : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have hd_eq : (d : Int) = -1 := by
          have hc : (DensePoly.C (d : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega
    · rcases hub with hone | hneg
      · have he_eq : (e : Int) = 1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have he_eq : (e : Int) = -1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega
  · have hk_eq : k = (-(d : Int)) * (e : Int) := by
      rw [heq, he, Int.natCast_mul, Int.neg_mul]
    have hC_split :
        DensePoly.C k = DensePoly.C (-(d : Int)) * DensePoly.C (e : Int) := by
      rw [hk_eq, zpoly_C_mul_C]
    rcases hirr.no_factors _ _ hC_split with hua | hub
    · rcases hua with hone | hneg
      · have hd_eq : (-(d : Int)) = 1 := by
          have hc : (DensePoly.C (-(d : Int))).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have hd_eq : (-(d : Int)) = -1 := by
          have hc : (DensePoly.C (-(d : Int))).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
    · rcases hub with hone | hneg
      · have he_eq : (e : Int) = 1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hone
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simpa using hc
        omega
      · have he_eq : (e : Int) = -1 := by
          have hc : (DensePoly.C (e : Int)).coeff 0 =
              (DensePoly.C (-1 : Int)).coeff 0 :=
            congrArg (fun p => DensePoly.coeff p 0) hneg
          rw [DensePoly.coeff_C, DensePoly.coeff_C] at hc
          simp at hc
        omega

/-- A monic integer polynomial of dense size two is irreducible. The proof
splits any factorization `f = a * b` by dense size: degree arithmetic forces
one factor to be a constant `±1`, so the constant factor is a `ZPoly` unit. -/
private theorem irreducible_of_size_two_monic
    (f : ZPoly) (hf_size : f.size = 2)
    (hf_monic : DensePoly.leadingCoeff f = (1 : Int)) :
    ZPoly.Irreducible f := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size
    change (0 : Nat) = 2 at hf_size
    omega
  have hf_pos : 0 < f.size := by omega
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hf_size
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hf_size
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    by_cases ha_zero : a = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, hb_zero]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hf_ab] at hab_size
    rw [hf_size] at hab_size
    have hsum : a.size + b.size = 3 := by omega
    have hlead :
        DensePoly.leadingCoeff a * DensePoly.leadingCoeff b = (1 : Int) := by
      have := ZPoly.leadingCoeff_mul_of_nonzero a b ha_zero hb_zero
      rw [← hf_ab] at this
      rw [hf_monic] at this
      exact this.symm
    have ha_size_le : a.size ≤ 2 := by omega
    have hb_size_le : b.size ≤ 2 := by omega
    have ha_size_eq_one_or_two : a.size = 1 ∨ a.size = 2 := by omega
    rcases ha_size_eq_one_or_two with ha_one | ha_two
    · -- a.size = 1, so a is constant; show IsUnit a
      left
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
      have ha_lead : DensePoly.leadingCoeff a = a.coeff 0 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last a (by omega)]
        congr 1
        omega
      rw [ha_lead] at hlead
      have ha_coeff_unit : a.coeff 0 = 1 ∨ a.coeff 0 = -1 :=
        int_factor_one_eq_unit hlead
      rcases ha_coeff_unit with hone | hneg
      · left
        rw [ha_eq, hone]
      · right
        rw [ha_eq, hneg]
    · -- a.size = 2, so b.size = 1; symmetric case
      right
      have hb_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
      have hb_lead : DensePoly.leadingCoeff b = b.coeff 0 := by
        rw [DensePoly.leadingCoeff_eq_coeff_last b (by omega)]
        congr 1
        omega
      rw [hb_lead] at hlead
      rw [Int.mul_comm] at hlead
      have hb_coeff_unit : b.coeff 0 = 1 ∨ b.coeff 0 = -1 :=
        int_factor_one_eq_unit hlead
      rcases hb_coeff_unit with hone | hneg
      · left
        rw [hb_eq, hone]
      · right
        rw [hb_eq, hneg]

/-- The integer indeterminate `X` is irreducible. -/
theorem irreducible_X : ZPoly.Irreducible ZPoly.X :=
  irreducible_of_size_two_monic ZPoly.X rfl rfl

/-- A primitive integer polynomial of dense size two is irreducible. Mirrors
`irreducible_of_size_two_monic` but uses primitivity (`content f = 1`) instead
of monicness to derive that a degree-zero factor must be `±1`: if `f = C c * b`
then `c` divides every coefficient of `f`, hence `c` divides `content f = 1`,
forcing `c ∈ {±1}`. -/
private theorem irreducible_of_size_two_primitive
    (f : ZPoly) (hf_size : f.size = 2)
    (hf_prim : ZPoly.Primitive f) :
    ZPoly.Irreducible f := by
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size
    change (0 : Nat) = 2 at hf_size
    omega
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hf_size
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hf_size
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    by_cases ha_zero : a = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, ha_zero, DensePoly.zero_mul]
    by_cases hb_zero : b = 0
    · exfalso
      apply hf_ne
      rw [hf_ab, hb_zero]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_zero
    have hb_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_zero
    have hab_size :
        (a * b).size = a.size + b.size - 1 :=
      ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_pos hb_pos
    rw [← hf_ab] at hab_size
    rw [hf_size] at hab_size
    have hsum : a.size + b.size = 3 := by omega
    have ha_size_le : a.size ≤ 2 := by omega
    have hb_size_le : b.size ≤ 2 := by omega
    have ha_size_eq_one_or_two : a.size = 1 ∨ a.size = 2 := by omega
    -- Helper: if `g = C c * h`, then `c` divides every coefficient of `g`,
    -- so `(c.natAbs : Int)` divides `content g`.
    have const_dvd_content :
        ∀ (g h : ZPoly) (c : Int),
          g = DensePoly.C c * h → ((c.natAbs : Int) : Int) ∣ ZPoly.content g := by
      intro g h c hg_eq
      apply ZPoly.dvd_content_of_nat_dvd_coeff
      intro n
      have hcoeff : g.coeff n = c * h.coeff n := by
        rw [hg_eq, C_mul_eq_scale,
          DensePoly.coeff_scale (R := Int) c h n (Int.mul_zero _)]
      refine Int.natAbs_dvd.mpr ?_
      rw [hcoeff]
      exact ⟨h.coeff n, rfl⟩
    -- Helper: if `c.natAbs` divides `1` and `c ≠ 0`, then `c ∈ {1, -1}`.
    have nat_factor_one :
        ∀ (c : Int), c ≠ 0 → ((c.natAbs : Int) : Int) ∣ (1 : Int) →
          c = 1 ∨ c = -1 := by
      intro c hc_ne hdvd
      have hnat_dvd : c.natAbs ∣ (1 : Nat) := by
        have := Int.ofNat_dvd.mp (show (c.natAbs : Int) ∣ ((1 : Nat) : Int) from hdvd)
        exact this
      have hnat_le : c.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
      have hnat_pos : 1 ≤ c.natAbs := by
        rcases Nat.eq_zero_or_pos c.natAbs with hzero | hpos
        · exact absurd (Int.natAbs_eq_zero.mp hzero) hc_ne
        · exact hpos
      have hnat_eq : c.natAbs = 1 := by omega
      rcases Int.natAbs_eq c with heq | heq
      · left; rw [heq, hnat_eq]; rfl
      · right; rw [heq, hnat_eq]; rfl
    rcases ha_size_eq_one_or_two with ha_one | ha_two
    · -- a.size = 1, so a is constant; show IsUnit a
      left
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_one
      have hf_eq : f = DensePoly.C (a.coeff 0) * b :=
        hf_ab.trans (congrArg (· * b) ha_eq)
      have hac_ne_zero : a.coeff 0 ≠ 0 := by
        intro h
        apply ha_zero
        rw [ha_eq, h]
        rfl
      have hcontent_one : ZPoly.content f = 1 := hf_prim
      have hac_dvd_content :
          ((a.coeff 0).natAbs : Int) ∣ ZPoly.content f :=
        const_dvd_content f b (a.coeff 0) hf_eq
      rw [hcontent_one] at hac_dvd_content
      rcases nat_factor_one (a.coeff 0) hac_ne_zero hac_dvd_content with
        hone | hneg
      · left; rw [ha_eq, hone]
      · right; rw [ha_eq, hneg]
    · -- a.size = 2, so b.size = 1; symmetric case via commutativity
      right
      have hb_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_one
      have hf_eq : f = DensePoly.C (b.coeff 0) * a :=
        (hf_ab.trans (DensePoly.mul_comm_poly a b)).trans
          (congrArg (· * a) hb_eq)
      have hbc_ne_zero : b.coeff 0 ≠ 0 := by
        intro h
        apply hb_zero
        rw [hb_eq, h]
        rfl
      have hcontent_one : ZPoly.content f = 1 := hf_prim
      have hbc_dvd_content :
          ((b.coeff 0).natAbs : Int) ∣ ZPoly.content f :=
        const_dvd_content f a (b.coeff 0) hf_eq
      rw [hcontent_one] at hbc_dvd_content
      rcases nat_factor_one (b.coeff 0) hbc_ne_zero hbc_dvd_content with
        hone | hneg
      · left; rw [hb_eq, hone]
      · right; rw [hb_eq, hneg]

/-- Mathlib-free Gauss reduction-mod-`p` transfer: a primitive integer
polynomial whose leading coefficient survives reduction modulo a prime `p` and
whose modular image is `FpPoly`-irreducible is itself `ZPoly.Irreducible`.

The `hnotConstant : 1 < f.size` precondition rules out the size-one constant
case explicitly: the executable `FpPoly.Irreducible` predicate only asserts the
factorization disjunction (it does not internally exclude constants the way
Mathlib's `_root_.Irreducible` does via `not_isUnit`), so the non-unit clause
for `f` is supplied at the `ZPoly` level. A primitive `ZPoly` of `size > 1` is
automatically not a `ZPoly` unit (units have size `1`).

Mathlib analog:
`HexBerlekampZassenhausMathlib.irreducible_of_isPrimitive_of_irreducible_map_intCast_zmod`
(`HexBerlekampZassenhausMathlib/IntReductionMod.lean:106`). -/
theorem Irreducible_of_modP_irreducible_of_primitive_of_admissible
    (f : ZPoly) (p : Nat) [ZMod64.Bounds p]
    (hprime : Nat.Prime p)
    (hprim : ZPoly.Primitive f)
    (hadm : leadingCoeffAdmissible f p)
    (hnotConstant : 1 < f.size)
    (hirr : FpPoly.Irreducible (ZPoly.modP p f)) :
    ZPoly.Irreducible f := by
  haveI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hprime
  have hf_size_pos : 0 < f.size :=
    leadingCoeffAdmissible_size_pos f p hadm
  have hf_ne : f ≠ 0 := by
    intro hzero
    rw [hzero] at hf_size_pos
    change (0 : Nat) < 0 at hf_size_pos
    omega
  have hmodP_f_ne : ZPoly.modP p f ≠ 0 :=
    modP_ne_zero_of_leadingCoeffAdmissible f p hadm
  have hmodP_f_size : (ZPoly.modP p f).size = f.size :=
    size_modP_eq_of_leadingCoeffAdmissible f p hadm
  refine
    { not_zero := hf_ne
      not_unit := ?_
      no_factors := ?_ }
  · -- `1 < f.size` rules out `f = C ±1`, the two possible unit shapes.
    intro hunit
    rcases hunit with hone | hneg
    · rw [hone] at hnotConstant
      have h1 : (DensePoly.C (1 : Int)).size = 1 := rfl
      omega
    · rw [hneg] at hnotConstant
      have hneg_size : (DensePoly.C (-1 : Int)).size = 1 := rfl
      omega
  · intro a b hf_ab
    have ha_ne : a ≠ 0 := by
      intro h
      apply hf_ne
      rw [hf_ab, h, DensePoly.zero_mul]
    have hb_ne : b ≠ 0 := by
      intro h
      apply hf_ne
      rw [hf_ab, h]
      change a * (0 : ZPoly) = 0
      rw [DensePoly.mul_comm_poly, DensePoly.zero_mul]
    have ha_size_pos : 0 < a.size := ZPoly.size_pos_of_ne_zero a ha_ne
    have hb_size_pos : 0 < b.size := ZPoly.size_pos_of_ne_zero b hb_ne
    have hab_size : f.size = a.size + b.size - 1 := by
      rw [hf_ab]
      exact ZPoly.mul_size_eq_top_succ_of_nonzero a b ha_size_pos hb_size_pos
    -- `modP p` distributes over multiplication.
    have hmodP_eq : ZPoly.modP p f = ZPoly.modP p a * ZPoly.modP p b := by
      rw [hf_ab, ZPoly.modP_mul]
    have hmodP_a_size_le : (ZPoly.modP p a).size ≤ a.size := size_modP_le p a
    have hmodP_b_size_le : (ZPoly.modP p b).size ≤ b.size := size_modP_le p b
    have hmodP_a_ne : ZPoly.modP p a ≠ 0 := by
      intro h
      apply hmodP_f_ne
      rw [hmodP_eq, h]
      exact DensePoly.zero_mul _
    have hmodP_b_ne : ZPoly.modP p b ≠ 0 := by
      intro h
      apply hmodP_f_ne
      rw [hmodP_eq, h]
      exact (DensePoly.mul_comm_poly (ZPoly.modP p a) 0).trans
        (DensePoly.zero_mul _)
    have hmodP_ab_size :
        (ZPoly.modP p a * ZPoly.modP p b).size =
          (ZPoly.modP p a).size + (ZPoly.modP p b).size - 1 :=
      FpPoly.size_mul_eq_add_sub_one
        (ZPoly.modP p a) (ZPoly.modP p b) hmodP_a_ne hmodP_b_ne
    have hmodP_a_size_pos : 0 < (ZPoly.modP p a).size :=
      FpPoly.size_pos_of_ne_zero hmodP_a_ne
    have hmodP_b_size_pos : 0 < (ZPoly.modP p b).size :=
      FpPoly.size_pos_of_ne_zero hmodP_b_ne
    -- Size arithmetic forces the modular images to retain the original sizes.
    have hsum :
        (ZPoly.modP p a).size + (ZPoly.modP p b).size = a.size + b.size := by
      have heq :
          (ZPoly.modP p a * ZPoly.modP p b).size = a.size + b.size - 1 := by
        rw [← hmodP_eq, hmodP_f_size, hab_size]
      rw [hmodP_ab_size] at heq
      omega
    have hmodP_a_size_eq : (ZPoly.modP p a).size = a.size := by omega
    have hmodP_b_size_eq : (ZPoly.modP p b).size = b.size := by omega
    -- `degree? = some 0` is equivalent to `size = 1` on a nonzero `DensePoly`.
    have hdeg_size :
        ∀ {g : FpPoly p}, g.degree? = some 0 → g.size = 1 := by
      intro g hdeg
      unfold DensePoly.degree? at hdeg
      by_cases hg_size : g.size = 0
      · rw [dif_pos hg_size] at hdeg
        simp at hdeg
      · rw [dif_neg hg_size] at hdeg
        injection hdeg with hdeg
        omega
    obtain ⟨_, hsplit⟩ := hirr
    have hcase := hsplit (ZPoly.modP p a) (ZPoly.modP p b) hmodP_eq.symm
    -- Local helper: a primitive product with one constant factor forces that
    -- factor to be `±1`, i.e. a `ZPoly` unit.
    have const_factor_isUnit :
        ∀ (g h : ZPoly) (c : Int),
          g = DensePoly.C c * h → c ≠ 0 → ZPoly.content g = 1 →
            ZPoly.IsUnit (DensePoly.C c) := by
      intro g h c hg_eq hc_ne hcontent_one
      have hc_dvd_content : ((c.natAbs : Int) : Int) ∣ ZPoly.content g := by
        apply ZPoly.dvd_content_of_nat_dvd_coeff
        intro n
        have hcoeff : g.coeff n = c * h.coeff n := by
          rw [hg_eq, ZPoly.C_mul_eq_scale,
            DensePoly.coeff_scale (R := Int) c h n (Int.mul_zero _)]
        refine Int.natAbs_dvd.mpr ?_
        rw [hcoeff]
        exact ⟨h.coeff n, rfl⟩
      rw [hcontent_one] at hc_dvd_content
      have hnat_dvd : c.natAbs ∣ (1 : Nat) := by
        have := Int.ofNat_dvd.mp (show (c.natAbs : Int) ∣ ((1 : Nat) : Int) from hc_dvd_content)
        exact this
      have hnat_le : c.natAbs ≤ 1 := Nat.le_of_dvd (by omega) hnat_dvd
      have hnat_pos : 1 ≤ c.natAbs := by
        rcases Nat.eq_zero_or_pos c.natAbs with hzero | hpos
        · exact absurd (Int.natAbs_eq_zero.mp hzero) hc_ne
        · exact hpos
      have hnat_eq : c.natAbs = 1 := by omega
      rcases Int.natAbs_eq c with heq | heq
      · left
        rw [heq, hnat_eq]
        rfl
      · right
        rw [heq, hnat_eq]
        rfl
    rcases hcase with hca | hcb
    · -- `modP p a` is constant ⇒ `a` is constant ⇒ `a` is a unit.
      left
      have hmodP_a_size_one : (ZPoly.modP p a).size = 1 := hdeg_size hca
      have ha_size_one : a.size = 1 := by omega
      have ha_eq : a = DensePoly.C (a.coeff 0) := eq_C_of_size_eq_one a ha_size_one
      have hac_ne : a.coeff 0 ≠ 0 := by
        intro h
        apply ha_ne
        rw [ha_eq, h]
        rfl
      have hf_eq : f = DensePoly.C (a.coeff 0) * b :=
        hf_ab.trans (congrArg (· * b) ha_eq)
      have hac_isUnit :=
        const_factor_isUnit f b (a.coeff 0) hf_eq hac_ne hprim
      rcases hac_isUnit with hone | hneg
      · left; rw [ha_eq]; exact hone
      · right; rw [ha_eq]; exact hneg
    · -- Symmetric case: `modP p b` is constant ⇒ `b` is constant ⇒ `b` is a unit.
      right
      have hmodP_b_size_one : (ZPoly.modP p b).size = 1 := hdeg_size hcb
      have hb_size_one : b.size = 1 := by omega
      have hb_eq : b = DensePoly.C (b.coeff 0) := eq_C_of_size_eq_one b hb_size_one
      have hbc_ne : b.coeff 0 ≠ 0 := by
        intro h
        apply hb_ne
        rw [hb_eq, h]
        rfl
      have hf_eq : f = DensePoly.C (b.coeff 0) * a :=
        (hf_ab.trans (DensePoly.mul_comm_poly a b)).trans
          (congrArg (· * a) hb_eq)
      have hbc_isUnit :=
        const_factor_isUnit f a (b.coeff 0) hf_eq hbc_ne hprim
      rcases hbc_isUnit with hone | hneg
      · left; rw [hb_eq]; exact hone
      · right; rw [hb_eq]; exact hneg

/-- Kernel-decidable irreducibility for a linear (dense size two) primitive
integer polynomial: both hypotheses are Boolean checks on literal data, so a
reified application discharges them with `Eq.refl true`. Public decide-slot
form of `irreducible_of_size_two_primitive` for the
`irreducibility`/`factor_poly` elaborators. -/
theorem irreducible_of_linear
    (f : ZPoly)
    (hsize : decide (f.size = 2) = true)
    (hcontent : decide (ZPoly.content f = 1) = true) :
    ZPoly.Irreducible f := by
  have hprim : ZPoly.Primitive f :=
    of_decide_eq_true (p := ZPoly.content f = 1) hcontent
  exact irreducible_of_size_two_primitive f (of_decide_eq_true hsize) hprim

end ZPoly

/-- `Hex.normalizeFactorSign` preserves `Hex.ZPoly.Irreducible`: the
sign-normalised polynomial equals either the original or its `-1` scaling,
and `-1` is a `ZPoly` unit, so the no-proper-factorization predicate
transfers. Mathlib-free counterpart of the Mathlib-side
`zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible`
(`HexBerlekampZassenhausMathlib`).  Consumed by the
Mathlib-free `factor_factors_irreducible` assembly (#4825). -/
theorem zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
    {f : ZPoly} (hirr : ZPoly.Irreducible f) :
    ZPoly.Irreducible (normalizeFactorSign f) := by
  unfold normalizeFactorSign
  by_cases hlc : DensePoly.leadingCoeff f < 0
  · rw [if_pos hlc]
    -- Sign-flipped branch: `DensePoly.scale (-1) f`.
    have hmulzero : (-1 : Int) * (0 : Int) = 0 := by decide
    -- `scale (-1)` is an involution on `ZPoly`.
    have hinvol : ∀ g : ZPoly,
        DensePoly.scale (-1 : Int) (DensePoly.scale (-1 : Int) g) = g := by
      intro g
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_scale (R := Int) (-1) g n hmulzero]
      omega
    have hscale_C_one : DensePoly.scale (-1 : Int) (DensePoly.C (1 : Int)) =
        DensePoly.C (-1 : Int) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_C, DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]; omega
    have hscale_C_neg_one : DensePoly.scale (-1 : Int) (DensePoly.C (-1 : Int)) =
        DensePoly.C (1 : Int) := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (-1) _ n hmulzero,
          DensePoly.coeff_C, DensePoly.coeff_C]
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn, if_neg hn]; omega
    have hscale_mul_left : ∀ a b : ZPoly,
        DensePoly.scale (-1 : Int) (a * b) = DensePoly.scale (-1 : Int) a * b := by
      intro a b
      rw [← ZPoly.C_mul_eq_scale, ← ZPoly.C_mul_eq_scale,
          DensePoly.mul_assoc_poly (S := Int)]
    refine
      { not_zero := ?_
        not_unit := ?_
        no_factors := ?_ }
    · -- `scale (-1) f ≠ 0`.
      intro h
      apply hirr.not_zero
      have hcong := congrArg (DensePoly.scale (-1 : Int)) h
      rw [hinvol, DensePoly.scale_neg_one_zero] at hcong
      exact hcong
    · -- `scale (-1) f` is not a unit.
      intro hunit
      apply hirr.not_unit
      rcases hunit with h1 | hnegone
      · -- `scale (-1) f = C 1` ⟹ `f = C (-1)`, which is a unit.
        right
        have hcong := congrArg (DensePoly.scale (-1 : Int)) h1
        rw [hinvol, hscale_C_one] at hcong
        exact hcong
      · -- `scale (-1) f = C (-1)` ⟹ `f = C 1`, which is a unit.
        left
        have hcong := congrArg (DensePoly.scale (-1 : Int)) hnegone
        rw [hinvol, hscale_C_neg_one] at hcong
        exact hcong
    · -- Factor preservation.
      intro a b hab
      have hf_eq : f = DensePoly.scale (-1 : Int) a * b := by
        have hcong := congrArg (DensePoly.scale (-1 : Int)) hab
        rw [hinvol, hscale_mul_left] at hcong
        exact hcong
      rcases hirr.no_factors _ _ hf_eq with hsa | hb
      · left
        rcases hsa with h1 | hnegone
        · -- `scale (-1) a = C 1` ⟹ `a = C (-1)`, a unit.
          right
          have hcong := congrArg (DensePoly.scale (-1 : Int)) h1
          rw [hinvol, hscale_C_one] at hcong
          exact hcong
        · -- `scale (-1) a = C (-1)` ⟹ `a = C 1`, a unit.
          left
          have hcong := congrArg (DensePoly.scale (-1 : Int)) hnegone
          rw [hinvol, hscale_C_neg_one] at hcong
          exact hcong
      · exact Or.inr hb
  · rw [if_neg hlc]
    exact hirr

/-- Every factor emitted by the extracted `X`-power normalization array is
irreducible. -/
theorem xPowerFactorArray_irreducible
    (power : Nat) (factor : ZPoly)
    (h : factor ∈ (xPowerFactorArray power).toList) :
    ZPoly.Irreducible factor := by
  rw [mem_xPowerFactorArray_eq_X power factor h]
  exact ZPoly.irreducible_X

/-- Reassembly preserves the irreducibility proof for normalization factors
coming specifically from the extracted power of `X`. -/
theorem reassemblePolynomialFactors_xPower_irreducible
    (d : FactorNormalizationData) (coreFactors : Array ZPoly) (factor : ZPoly)
    (_hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList)
    (hx : factor ∈ (xPowerFactorArray d.xPower).toList) :
    ZPoly.Irreducible factor :=
  xPowerFactorArray_irreducible d.xPower factor hx

/-- Lift core-factor irreducibility through the reassembly.  When the
repeated-part expansion fully consumes its residual (so the reassembly emits
only `X` powers and the supplied core factors), every emitted raw factor is
irreducible.  This is the Mathlib-free "reassemble lift" consumed by the
assembled per-branch output theorem to discharge the `xPower` half of each
branch automatically. -/
theorem reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
    (d : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hcomplete : reassemblyExpansionComplete d coreFactors)
    (h_core : ∀ factor ∈ coreFactors.toList, ZPoly.Irreducible factor)
    {factor : ZPoly}
    (hmem : factor ∈ (reassemblePolynomialFactors d coreFactors).toList) :
    ZPoly.Irreducible factor := by
  rcases reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
      d coreFactors factor hcomplete hmem with hx | hcore
  · exact xPowerFactorArray_irreducible d.xPower factor hx
  · exact h_core factor hcore

/-- Membership classifier for the constant square-free-core branch. The only
raw factors requiring irreducibility content are extracted powers of `X`; the
singleton core factor is `1`, and any repeated-part fallback is identified
separately for later expansion through actual core factors. -/
theorem reassemblePolynomialFactors_constant_irreducible_or_repeated_or_one
    (d : FactorNormalizationData) {factor : ZPoly}
    (hcore : d.squareFreeCore = 1)
    (hmem : factor ∈
      (reassemblePolynomialFactors d #[d.squareFreeCore]).toList) :
    ZPoly.Irreducible factor ∨
      factor ∈ (repeatedPartFactorArray d.repeatedPart).toList ∨
      factor = 1 := by
  rcases reassemblePolynomialFactors_mem d #[d.squareFreeCore] factor hmem with
    hprefix | hcore_mem
  · unfold polynomialNormalizationPrefixFactors at hprefix
    rw [Array.toList_append] at hprefix
    simp only [List.mem_append] at hprefix
    cases hprefix with
    | inl hx =>
        exact Or.inl (xPowerFactorArray_irreducible d.xPower factor hx)
    | inr hrep =>
        exact Or.inr (Or.inl hrep)
  · have hfactor : factor = d.squareFreeCore := by
      simpa using hcore_mem
    exact Or.inr (Or.inr (by simpa [hcore] using hfactor))

/-- The monic linear factor `X - r` is irreducible over `ZPoly`. -/
private theorem irreducible_linearFactorForRoot (r : Int) :
    ZPoly.Irreducible (linearFactorForRoot r) :=
  ZPoly.irreducible_of_size_two_monic (linearFactorForRoot r)
    (linearFactorForRoot_size_eq_two r)
    (leadingCoeff_linearFactorForRoot r)

/--
The primitive square-free layer in normalization reassembles the extracted
`X`-free primitive core up to the rational unit introduced by clearing
denominators.
-/
theorem normalizeForFactor_reassembles (f : ZPoly) :
    let normalized := normalizeForFactor f
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (normalized.squareFreeCore * normalized.repeatedPart)) := by
  unfold normalizeForFactor
  simp only
  exact primitiveSquareFreeDecomposition_reassembles_xfree_over_rat
    (ZPoly.extractXPower (ZPoly.primitivePart f)).core

/--
Replacing the square-free core by a product-equivalent factor array preserves
the rational-associate normalization invariant for the extracted primitive core.
-/
theorem reassembleNormalizedFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData) (coreFactors : Array ZPoly)
    (hnormalized : normalizeForFactor f = normalized)
    (hcore : Array.polyProduct coreFactors = normalized.squareFreeCore) :
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (Array.polyProduct coreFactors * normalized.repeatedPart)) := by
  subst normalized
  have hnormalized := normalizeForFactor_reassembles f
  change
    ∃ unit : Rat,
      ZPoly.toRatPoly (normalizeForFactor f).xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly
            ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) at hnormalized
  simpa [hcore] using hnormalized

/--
For constant square-free cores, the normalization-only factor array preserves the
rational-associate normalization invariant for the extracted primitive core.
-/
theorem normalizedConstantFactors_product
    (f : ZPoly) (normalized : FactorNormalizationData)
    (hnormalized : normalizeForFactor f = normalized)
    (hconst : normalized.squareFreeCore.degree?.getD 0 = 0) :
    ∃ unit : Rat,
      ZPoly.toRatPoly normalized.xFreePrimitive =
        DensePoly.scale unit
          (ZPoly.toRatPoly (normalized.squareFreeCore * normalized.repeatedPart)) := by
  subst normalized
  by_cases hcore : (normalizeForFactor f).squareFreeCore = 1
  · simpa [normalizedConstantFactors, hcore] using normalizeForFactor_reassembles f
  · simpa [normalizedConstantFactors, hcore] using normalizeForFactor_reassembles f

/--
The `X`-free part of the primitive part of a nonzero integer polynomial is itself
primitive. Stripping initial zero coefficients does not introduce a common factor
because the original primitive part already has unit content.
-/
theorem extractXPower_core_primitive_of_ne_zero
    (f : ZPoly) (hf : f ≠ 0) :
    ZPoly.Primitive (ZPoly.extractXPower (ZPoly.primitivePart f)).core := by
  -- Step 1: shift xData.power xData.core = primitivePart f.
  have hshift :
      DensePoly.shift (ZPoly.extractXPower (ZPoly.primitivePart f)).power
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core =
        ZPoly.primitivePart f := by
    have hex :
        Array.polyProduct
          (xPowerFactorArray (ZPoly.extractXPower (ZPoly.primitivePart f)).power ++
            #[(ZPoly.extractXPower (ZPoly.primitivePart f)).core]) =
          ZPoly.primitivePart f :=
      extractXPower_product (ZPoly.primitivePart f)
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton, polyProduct_xPowerFactorArray_mul] at hex
    exact hex
  -- Step 2: f ≠ 0 → content f ≠ 0.
  have hcontent_f_ne : ZPoly.content f ≠ 0 := by
    intro hcontent
    apply hf
    have hreconstruct := ZPoly.content_mul_primitivePart f
    rw [hcontent] at hreconstruct
    have hzero : DensePoly.scale (0 : Int) (ZPoly.primitivePart f) = 0 := by
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_scale (R := Int) (0 : Int) (ZPoly.primitivePart f) n
        (Int.zero_mul 0)]
      rw [DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [hzero] at hreconstruct
    exact hreconstruct.symm
  -- Step 3: content (primitivePart f) = 1.
  have hcontent_pf : ZPoly.content (ZPoly.primitivePart f) = 1 :=
    ZPoly.primitivePart_primitive f hcontent_f_ne
  -- Step 4: every coefficient of primitivePart f is divisible by content xData.core.
  have hdvd : ∀ n,
      ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core ∣
        (ZPoly.primitivePart f).coeff n := by
    intro n
    have hcoeff_eq :
        (ZPoly.primitivePart f).coeff n =
          (DensePoly.shift (ZPoly.extractXPower (ZPoly.primitivePart f)).power
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).coeff n :=
      congrArg (fun p : ZPoly => p.coeff n) hshift.symm
    rw [hcoeff_eq, DensePoly.coeff_shift]
    by_cases hn : n < (ZPoly.extractXPower (ZPoly.primitivePart f)).power
    · rw [if_pos hn]
      exact ⟨0, by show (0 : Int) = _ * 0; rw [Int.mul_zero]⟩
    · rw [if_neg hn]
      exact DensePoly.content_dvd_coeff
        (ZPoly.extractXPower (ZPoly.primitivePart f)).core
        (n - (ZPoly.extractXPower (ZPoly.primitivePart f)).power)
  -- Step 5: content xData.core is non-negative.
  have hcontent_nonneg :
      0 ≤ ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core := by
    show 0 ≤ DensePoly.content _
    rw [DensePoly.content]
    exact Int.natCast_nonneg _
  have hd_int :
      ((ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) =
        ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core :=
    Int.toNat_of_nonneg hcontent_nonneg
  have hdvd_d :
      ∀ n,
        ((ZPoly.content
            (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) ∣
          (ZPoly.primitivePart f).coeff n := by
    intro n
    rw [hd_int]
    exact hdvd n
  -- Step 6: apply the nat_eq_one helper.
  have hd_eq :
      (ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat = 1 :=
    DensePoly.nat_eq_one_of_content_eq_one_of_nat_dvd_coeff
      (ZPoly.primitivePart f) _
      (by simpa [ZPoly.content] using hcontent_pf)
      hdvd_d
  show ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core = 1
  have hcast :
      ((ZPoly.content (ZPoly.extractXPower (ZPoly.primitivePart f)).core).toNat : Int) =
        (1 : Int) := by exact_mod_cast hd_eq
  rw [hd_int] at hcast
  exact hcast

private theorem normalizeForFactor_reassembles_with_signed_unit
    (f : ZPoly) (hf : f ≠ 0) :
    ∃ ε : Int, (ε = 1 ∨ ε = -1) ∧
      DensePoly.scale (ZPoly.content f * ε)
        (DensePoly.shift (normalizeForFactor f).xPower
          ((normalizeForFactor f).squareFreeCore * (normalizeForFactor f).repeatedPart)) =
        f := by
  let xData := ZPoly.extractXPower (ZPoly.primitivePart f)
  let sqData := ZPoly.primitiveSquareFreeDecomposition xData.core
  have hcore_primitive : ZPoly.Primitive xData.core := by
    simpa [xData] using extractXPower_core_primitive_of_ne_zero f hf
  have hcore_ne : xData.core ≠ 0 := by
    intro hzero
    have hcontent : ZPoly.content xData.core = 0 := by
      rw [hzero]
      simp [ZPoly.content, DensePoly.content_zero]
    rw [ZPoly.Primitive, hcontent] at hcore_primitive
    contradiction
  have hprimitive_core : ZPoly.primitivePart xData.core = xData.core :=
    ZPoly.primitivePart_eq_self_of_primitive xData.core hcore_primitive
  have hshift_core :
      DensePoly.shift xData.power xData.core = ZPoly.primitivePart f := by
    have hex :
        Array.polyProduct (xPowerFactorArray xData.power ++ #[xData.core]) =
          ZPoly.primitivePart f := by
      simpa [xData] using extractXPower_product (ZPoly.primitivePart f)
    rw [ZPoly.polyProduct_append, ZPoly.polyProduct_singleton, polyProduct_xPowerFactorArray_mul] at hex
    exact hex
  rcases ZPoly.primitiveSquareFreeDecomposition_reassembly_signed xData.core hcore_ne with
    ⟨ε, hε, hsq⟩
  refine ⟨ε, hε, ?_⟩
  have hsq_core :
      DensePoly.scale ε (sqData.squareFreeCore * sqData.repeatedPart) = xData.core := by
    simpa [sqData, hprimitive_core] using hsq
  have hshift_sq :
      DensePoly.scale ε
          (DensePoly.shift xData.power (sqData.squareFreeCore * sqData.repeatedPart)) =
        DensePoly.shift xData.power xData.core := by
    rw [← shift_scale_int]
    exact congrArg (DensePoly.shift xData.power) hsq_core
  have hscaled :
      DensePoly.scale (ZPoly.content f)
          (DensePoly.scale ε
            (DensePoly.shift xData.power (sqData.squareFreeCore * sqData.repeatedPart))) =
        DensePoly.scale (ZPoly.content f) (DensePoly.shift xData.power xData.core) := by
    rw [hshift_sq]
  rw [int_scale_scale] at hscaled
  rw [hshift_core, ZPoly.content_mul_primitivePart] at hscaled
  simpa [normalizeForFactor, xData, sqData] using hscaled

end Hex
