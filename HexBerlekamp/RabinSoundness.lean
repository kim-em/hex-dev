import HexBerlekamp.Irreducibility
import HexBerlekamp.Factor
import HexPolyFp.Compose
import HexPolyFp.Quotient
import HexPolyFp.QuotientFrobenius
import HexArith.Nat.Pow

/-!
Project-side soundness of `Berlekamp.rabinTest` against
`FpPoly.Irreducible`.

The executable irreducibility surface in `HexBerlekamp/Irreducibility.lean`
gives a `Bool` predicate `rabinTest f hmonic` capturing the three legs of
Rabin's criterion phrased through `frobeniusXPowMod`. This module reduces
`rabinTest = true` to the project-side `FpPoly.Irreducible` predicate from
`HexPolyFp/Basic.lean`, without going through Mathlib.

The proof reduces to a small set of foundational lemmas tracked as
their own follow-up issues; `rabinTest_imp_irreducible` only orchestrates
them in a single contrapositive argument.
-/

namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/--
The polynomial `X^(p^k) - X` viewed inside the executable `FpPoly p` model.

Used to phrase the absolute (not modular) divisibility leg `f ∣ X^(p^n) - X`
underlying Rabin's test.
-/
def xPowSubX (k : Nat) : FpPoly p :=
  DensePoly.monomial (p ^ k) (1 : ZMod64 p) - FpPoly.X

/-! ### Prime-field linear product -/

/-- The executable product `∏ c ∈ F_p, (X - c)` over canonical residues. -/
def primeFieldLinearProduct : FpPoly p :=
  (ZMod64.values p).foldl
    (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1

/-- The linear factor corresponding to a prime-field residue. -/
def primeFieldLinearFactor (c : ZMod64 p) : FpPoly p :=
  FpPoly.X - FpPoly.C c

private theorem primeFieldLinearFactor_dvd_foldl_of_dvd_acc
    (d : FpPoly p) (xs : List (ZMod64 p)) (acc : FpPoly p)
    (hacc : d ∣ acc) :
    d ∣ xs.foldl (fun acc c => acc * primeFieldLinearFactor c) acc := by
  induction xs generalizing acc with
  | nil =>
      exact hacc
  | cons c xs ih =>
      rcases hacc with ⟨q, hq⟩
      apply ih
      refine ⟨q * primeFieldLinearFactor c, ?_⟩
      calc
        acc * primeFieldLinearFactor c =
            (d * q) * primeFieldLinearFactor c := by rw [hq]
        _ = d * (q * primeFieldLinearFactor c) := FpPoly.mul_assoc d q _

private theorem primeFieldLinearFactor_dvd_foldl_of_mem
    (c : ZMod64 p) (xs : List (ZMod64 p)) (acc : FpPoly p)
    (hmem : c ∈ xs) :
    primeFieldLinearFactor c ∣
      xs.foldl (fun acc d => acc * primeFieldLinearFactor d) acc := by
  induction xs generalizing acc with
  | nil =>
      cases hmem
  | cons d xs ih =>
      simp only [List.mem_cons] at hmem
      simp only [List.foldl_cons]
      rcases hmem with hcd | htail
      · subst d
        apply primeFieldLinearFactor_dvd_foldl_of_dvd_acc
        refine ⟨acc, ?_⟩
        exact FpPoly.mul_comm acc (primeFieldLinearFactor c)
      · exact ih (acc * primeFieldLinearFactor d) htail

/--
Every field element contributes its linear factor to the canonical
prime-field product. This is the divisibility/root-coverage form used by
the subsequent `X^p - X` product-identity assembly.
-/
theorem primeFieldLinearFactor_dvd_primeFieldLinearProduct (c : ZMod64 p) :
    primeFieldLinearFactor c ∣ primeFieldLinearProduct (p := p) := by
  unfold primeFieldLinearProduct
  exact primeFieldLinearFactor_dvd_foldl_of_mem c (ZMod64.values p) 1
    (ZMod64.mem_values c)

/-- The canonical product has one listed linear factor for each residue. -/
@[simp] theorem primeFieldLinearProduct_factor_count :
    (ZMod64.values p).length = p :=
  ZMod64.values_length (p := p)

/-! ### CRT representatives for Berlekamp completeness -/

/--
The zero-one CRT representative used to separate a coprime product
`a * b`: it is congruent to `0` modulo `a` and to `1` modulo `b` when
`s * a + t * b = 1`.
-/
def crtZeroOneCandidate (a b s t : FpPoly p) : FpPoly p :=
  DensePoly.polyCRT a b 0 1 s t

/-- The zero-one CRT representative is congruent to `0` modulo the left factor. -/
theorem crtZeroOneCandidate_congr_zero_left
    (a b s t : FpPoly p) (hbez : s * a + t * b = 1) :
    DensePoly.Congr (crtZeroOneCandidate a b s t) 0 a := by
  unfold crtZeroOneCandidate
  simpa using
    (DensePoly.polyCRT_congr_fst a b (0 : FpPoly p) (1 : FpPoly p) s t hbez)

/-- The zero-one CRT representative is congruent to `1` modulo the right factor. -/
theorem crtZeroOneCandidate_congr_one_right
    (a b s t : FpPoly p) (hbez : s * a + t * b = 1) :
    DensePoly.Congr (crtZeroOneCandidate a b s t) 1 b := by
  unfold crtZeroOneCandidate
  simpa using
    (DensePoly.polyCRT_congr_snd a b (0 : FpPoly p) (1 : FpPoly p) s t hbez)

/-- Monic reduction of the zero-one CRT representative modulo the left factor. -/
theorem crtZeroOneCandidate_modByMonic_zero_left
    [ZMod64.PrimeModulus p] (a b s t : FpPoly p)
    (ha : DensePoly.Monic a) (hbez : s * a + t * b = 1) :
    DensePoly.modByMonic (crtZeroOneCandidate a b s t) a ha =
      DensePoly.modByMonic (0 : FpPoly p) a ha := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  unfold crtZeroOneCandidate
  simpa using
    (@DensePoly.polyCRT_modByMonic_fst (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) a b
      (0 : FpPoly p) (1 : FpPoly p) s t ha hbez)

/-- Monic reduction of the zero-one CRT representative modulo the right factor. -/
theorem crtZeroOneCandidate_modByMonic_one_right
    [ZMod64.PrimeModulus p] (a b s t : FpPoly p)
    (hb : DensePoly.Monic b) (hbez : s * a + t * b = 1) :
    DensePoly.modByMonic (crtZeroOneCandidate a b s t) b hb =
      DensePoly.modByMonic (1 : FpPoly p) b hb := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  unfold crtZeroOneCandidate
  simpa using
    (@DensePoly.polyCRT_modByMonic_snd (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) a b
      (0 : FpPoly p) (1 : FpPoly p) s t hb hbez)

/-- Remainder form of the zero residue modulo the left factor. -/
theorem crtZeroOneCandidate_mod_zero_left
    [ZMod64.PrimeModulus p] (a b s t : FpPoly p)
    (ha : DensePoly.Monic a) (hbez : s * a + t * b = 1) :
    crtZeroOneCandidate a b s t % a = (0 : FpPoly p) % a := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  unfold crtZeroOneCandidate
  simpa using
    (@DensePoly.polyCRT_mod_fst (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) a b
      (0 : FpPoly p) (1 : FpPoly p) s t ha hbez)

/-- Remainder form of the one residue modulo the right factor. -/
theorem crtZeroOneCandidate_mod_one_right
    [ZMod64.PrimeModulus p] (a b s t : FpPoly p)
    (hb : DensePoly.Monic b) (hbez : s * a + t * b = 1) :
    crtZeroOneCandidate a b s t % b = (1 : FpPoly p) % b := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  unfold crtZeroOneCandidate
  simpa using
    (@DensePoly.polyCRT_mod_snd (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) a b
      (0 : FpPoly p) (1 : FpPoly p) s t hb hbez)

/-- The same zero-one CRT representative, using the executable xgcd coefficients. -/
def crtZeroOneXGCDCandidate (a b : FpPoly p) : FpPoly p :=
  let r := DensePoly.xgcd a b
  crtZeroOneCandidate a b r.left r.right

/-- If the executable gcd is `1`, xgcd supplies CRT-ready coefficients. -/
theorem xgcd_bezout_of_gcd_eq_one
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hgcd : DensePoly.gcd a b = 1) :
    (DensePoly.xgcd a b).left * a + (DensePoly.xgcd a b).right * b = 1 := by
  haveI : DensePoly.GcdLaws (ZMod64 p) := inferInstance
  have hgcd' : (DensePoly.xgcd a b).gcd = 1 := by
    simpa [DensePoly.gcd] using hgcd
  simpa [hgcd'] using DensePoly.xgcd_bezout a b

/-- The xgcd-backed zero-one CRT representative is congruent to `0` on the left. -/
theorem crtZeroOneXGCDCandidate_congr_zero_left
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hgcd : DensePoly.gcd a b = 1) :
    DensePoly.Congr (crtZeroOneXGCDCandidate a b) 0 a := by
  unfold crtZeroOneXGCDCandidate
  exact crtZeroOneCandidate_congr_zero_left a b
    (DensePoly.xgcd a b).left (DensePoly.xgcd a b).right
    (xgcd_bezout_of_gcd_eq_one a b hgcd)

/-- The xgcd-backed zero-one CRT representative is congruent to `1` on the right. -/
theorem crtZeroOneXGCDCandidate_congr_one_right
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hgcd : DensePoly.gcd a b = 1) :
    DensePoly.Congr (crtZeroOneXGCDCandidate a b) 1 b := by
  unfold crtZeroOneXGCDCandidate
  exact crtZeroOneCandidate_congr_one_right a b
    (DensePoly.xgcd a b).left (DensePoly.xgcd a b).right
    (xgcd_bezout_of_gcd_eq_one a b hgcd)

/-- Remainder form of the xgcd-backed zero residue modulo the left factor. -/
theorem crtZeroOneXGCDCandidate_mod_zero_left
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hgcd : DensePoly.gcd a b = 1) :
    crtZeroOneXGCDCandidate a b % a = (0 : FpPoly p) % a := by
  unfold crtZeroOneXGCDCandidate
  exact crtZeroOneCandidate_mod_zero_left a b
    (DensePoly.xgcd a b).left (DensePoly.xgcd a b).right ha
    (xgcd_bezout_of_gcd_eq_one a b hgcd)

/-- Remainder form of the xgcd-backed one residue modulo the right factor. -/
theorem crtZeroOneXGCDCandidate_mod_one_right
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hb : DensePoly.Monic b) (hgcd : DensePoly.gcd a b = 1) :
    crtZeroOneXGCDCandidate a b % b = (1 : FpPoly p) % b := by
  unfold crtZeroOneXGCDCandidate
  exact crtZeroOneCandidate_mod_one_right a b
    (DensePoly.xgcd a b).left (DensePoly.xgcd a b).right hb
    (xgcd_bezout_of_gcd_eq_one a b hgcd)

private theorem congr_of_congr_mul_left
    {x y a b : FpPoly p} (h : DensePoly.Congr x y (a * b)) :
    DensePoly.Congr x y a := by
  rcases h with ⟨r, hr⟩
  refine ⟨b * r, ?_⟩
  rw [hr, FpPoly.mul_assoc]

private theorem congr_of_congr_mul_right
    {x y a b : FpPoly p} (h : DensePoly.Congr x y (a * b)) :
    DensePoly.Congr x y b := by
  rcases h with ⟨r, hr⟩
  refine ⟨a * r, ?_⟩
  calc
    x - y = (a * b) * r := hr
    _ = a * (b * r) := FpPoly.mul_assoc a b r
    _ = b * (a * r) := by
      calc
        a * (b * r) = (a * b) * r := (FpPoly.mul_assoc a b r).symm
        _ = (b * a) * r := by rw [FpPoly.mul_comm a b]
        _ = b * (a * r) := FpPoly.mul_assoc b a r

private theorem zmod64_one_ne_zero_of_prime [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ (0 : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

/-- The listed prime-field linear factors are genuinely degree-one candidates. -/
theorem primeFieldLinearFactor_coeff_one (c : ZMod64 p) :
    (primeFieldLinearFactor c).coeff 1 = (1 : ZMod64 p) := by
  unfold primeFieldLinearFactor FpPoly.X FpPoly.C
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_C]
  simp
  show (1 : ZMod64 p) - 0 = 1
  grind

/-- No listed prime-field linear factor is the zero polynomial. -/
theorem primeFieldLinearFactor_ne_zero
    [ZMod64.PrimeModulus p] (c : ZMod64 p) :
    primeFieldLinearFactor c ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 1) hzero
  change (primeFieldLinearFactor c).coeff 1 = (0 : FpPoly p).coeff 1 at hcoeff
  rw [primeFieldLinearFactor_coeff_one c, DensePoly.coeff_zero] at hcoeff
  exact zmod64_one_ne_zero_of_prime hcoeff

private theorem constant_eq_zero_of_mod_eq_zero
    [ZMod64.PrimeModulus p] {a : FpPoly p} {c : ZMod64 p}
    (ha_pos : 0 < a.degree?.getD 0)
    (hmod : (DensePoly.C c : FpPoly p) % a = (0 : FpPoly p) % a) :
    c = 0 := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hC : (DensePoly.C c : FpPoly p) % a = DensePoly.C c := by
    apply DensePoly.mod_eq_self_of_degree_lt
    rw [DensePoly.degree?_C_getD]
    exact ha_pos
  have hzero : (0 : FpPoly p) % a = 0 := by
    exact DensePoly.zero_mod_eq_zero_core (S := ZMod64 p) a
  have hpoly : (DensePoly.C c : FpPoly p) = 0 := by
    simpa [hC, hzero] using hmod
  have hcoeff := congrArg (fun q : FpPoly p => q.coeff 0) hpoly
  simpa using hcoeff

private theorem constant_eq_one_of_mod_eq_one
    [ZMod64.PrimeModulus p] {b : FpPoly p} {c : ZMod64 p}
    (hb_pos : 0 < b.degree?.getD 0)
    (hmod : (DensePoly.C c : FpPoly p) % b = (1 : FpPoly p) % b) :
    c = 1 := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hC : (DensePoly.C c : FpPoly p) % b = DensePoly.C c := by
    apply DensePoly.mod_eq_self_of_degree_lt
    rw [DensePoly.degree?_C_getD]
    exact hb_pos
  have hone_deg : (1 : FpPoly p).degree?.getD 0 < b.degree?.getD 0 := by
    change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 < b.degree?.getD 0
    rw [DensePoly.degree?_C_getD]
    exact hb_pos
  have hone : (1 : FpPoly p) % b = 1 := by
    exact DensePoly.mod_eq_self_of_degree_lt (1 : FpPoly p) b hone_deg
  have hpoly : (DensePoly.C c : FpPoly p) = 1 := by
    simpa [hC, hone] using hmod
  have hcoeff := congrArg (fun q : FpPoly p => q.coeff 0) hpoly
  have hC_coeff : (DensePoly.C c : FpPoly p).coeff 0 = c := by
    rw [DensePoly.coeff_C]
    simp
  have hone_coeff : (1 : FpPoly p).coeff 0 = (1 : ZMod64 p) := by
    change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (1 : ZMod64 p)
    rw [DensePoly.coeff_C]
    simp
  exact hC_coeff.symm.trans (hcoeff.trans hone_coeff)

/--
The zero-one CRT representative is not congruent to a constant modulo
`a * b` when both factors have positive degree.
-/
theorem crtZeroOneCandidate_not_congr_constant_mod_product
    [ZMod64.PrimeModulus p] (a b s t : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hbez : s * a + t * b = 1) (c : ZMod64 p) :
    ¬ DensePoly.Congr (crtZeroOneCandidate a b s t) (DensePoly.C c) (a * b) := by
  intro hconst
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hconst_left :
      crtZeroOneCandidate a b s t % a = (DensePoly.C c : FpPoly p) % a :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ _ (congr_of_congr_mul_left hconst)
  have hconst_right :
      crtZeroOneCandidate a b s t % b = (DensePoly.C c : FpPoly p) % b :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance inferInstance
      (ZMod64.instDivModLawsZMod64Fp p) _ _ _ (congr_of_congr_mul_right hconst)
  have hc_zero : c = 0 := by
    apply constant_eq_zero_of_mod_eq_zero (a := a) ha_pos
    exact hconst_left.symm.trans
      (crtZeroOneCandidate_mod_zero_left a b s t ha hbez)
  have hc_one : c = 1 := by
    apply constant_eq_one_of_mod_eq_one (b := b) hb_pos
    exact hconst_right.symm.trans
      (crtZeroOneCandidate_mod_one_right a b s t hb hbez)
  exact zmod64_one_ne_zero_of_prime (hc_one.symm.trans hc_zero)

/-- XGCD-backed specialization of `crtZeroOneCandidate_not_congr_constant_mod_product`. -/
theorem crtZeroOneXGCDCandidate_not_congr_constant_mod_product
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hgcd : DensePoly.gcd a b = 1) (c : ZMod64 p) :
    ¬ DensePoly.Congr (crtZeroOneXGCDCandidate a b) (DensePoly.C c) (a * b) := by
  unfold crtZeroOneXGCDCandidate
  exact crtZeroOneCandidate_not_congr_constant_mod_product a b
    (DensePoly.xgcd a b).left (DensePoly.xgcd a b).right
    ha hb ha_pos hb_pos (xgcd_bezout_of_gcd_eq_one a b hgcd) c

section

variable [ZMod64.PrimeModulus p]

/-! ### Foundational lemmas

The following declarations are stated with proofs deferred to their own
follow-up issues. Every other declaration in this file is a small
orchestration step on top of them. -/

/-- Divisibility by `f` is equivalent to a zero canonical remainder. -/
theorem dvd_iff_mod_eq_zero (f q : FpPoly p) :
    f ∣ q ↔ q % f = 0 := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := inferInstance
  refine ⟨DensePoly.mod_eq_zero_of_dvd q f, ?_⟩
  intro hmod
  refine ⟨q / f, ?_⟩
  have h := DensePoly.div_mul_add_mod q f
  rw [hmod, FpPoly.add_zero, FpPoly.mul_comm] at h
  exact h.symm

/-- `linearPow` has the same canonical remainder for bases with the same
canonical remainder. -/
theorem linearPow_mod_eq_of_mod_eq_mod (f h r : FpPoly p) (n : Nat)
    (hmod : h % f = r % f) :
    FpPoly.linearPow h n % f = FpPoly.linearPow r n % f := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      calc
        FpPoly.linearPow h (n + 1) % f
            = (FpPoly.linearPow h n * h) % f := by rw [FpPoly.linearPow_succ]
        _ = ((FpPoly.linearPow h n % f) * (h % f)) % f :=
              @DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance
                inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ f
        _ = ((FpPoly.linearPow r n % f) * (r % f)) % f := by rw [ih, hmod]
        _ = (FpPoly.linearPow r n * r) % f :=
              (@DensePoly.mod_mul_mod (ZMod64 p) inferInstance inferInstance
                inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ f).symm
        _ = FpPoly.linearPow r (n + 1) % f := by rw [FpPoly.linearPow_succ]

/-- Polynomial congruence modulo `f` is preserved by `linearPow`. -/
theorem linearPow_congr_of_congr (f h r : FpPoly p) (n : Nat)
    (hcongr : DensePoly.Congr h r f) :
    DensePoly.Congr (FpPoly.linearPow h n) (FpPoly.linearPow r n) f := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  apply @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p)
  exact linearPow_mod_eq_of_mod_eq_mod f h r n
    (@DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) h r f hcongr)

omit [ZMod64.PrimeModulus p] in
/-- Polynomial congruence modulo `f` is preserved by subtraction. -/
theorem congr_sub_of_congr (f a b c d : FpPoly p)
    (hab : DensePoly.Congr a b f) (hcd : DensePoly.Congr c d f) :
    DensePoly.Congr (a - c) (b - d) f := by
  have heq : (a - c) - (b - d) = (a - b) - (c - d) := by
    apply DensePoly.ext_coeff
    intro i
    repeat rw [DensePoly.coeff_sub_ring]
    grind
  rw [DensePoly.Congr, heq]
  exact DensePoly.dvd_sub_poly hab hcd

/--
Membership in the Frobenius fixed-kernel depends only on the residue class
modulo the ambient polynomial.

This is the representative-reduction lemma needed by the Berlekamp CRT
construction: reducing a candidate modulo `f` preserves and reflects the
absolute divisibility condition `f ∣ h^(p^k) - h`.
-/
theorem dvd_linearPow_sub_self_mod_iff
    (f h : FpPoly p) (k : Nat) :
    f ∣ (FpPoly.linearPow h (p ^ k) - h) ↔
      f ∣ (FpPoly.linearPow (h % f) (p ^ k) - (h % f)) := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hbase_mod : h % f = (h % f) % f := (DensePoly.mod_mod h f).symm
  have hpow_mod :
      FpPoly.linearPow h (p ^ k) % f =
        FpPoly.linearPow (h % f) (p ^ k) % f :=
    linearPow_mod_eq_of_mod_eq_mod f h (h % f) (p ^ k) hbase_mod
  have hpow_congr :
      DensePoly.Congr (FpPoly.linearPow h (p ^ k))
        (FpPoly.linearPow (h % f) (p ^ k)) f :=
    @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hpow_mod
  have hbase_congr : DensePoly.Congr h (h % f) f :=
    @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hbase_mod
  have hdiff_congr :
      DensePoly.Congr (FpPoly.linearPow h (p ^ k) - h)
        (FpPoly.linearPow (h % f) (p ^ k) - (h % f)) f :=
    congr_sub_of_congr f _ _ _ _ hpow_congr hbase_congr
  have hdiff_mod :
      (FpPoly.linearPow h (p ^ k) - h) % f =
        (FpPoly.linearPow (h % f) (p ^ k) - (h % f)) % f :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hdiff_congr
  rw [dvd_iff_mod_eq_zero, dvd_iff_mod_eq_zero, hdiff_mod]

omit [ZMod64.PrimeModulus p] in
private theorem linearPow_zero_of_pos (n : Nat) (hn : 0 < n) :
    FpPoly.linearPow (0 : FpPoly p) n = 0 := by
  have hsucc : ∀ m : Nat, FpPoly.linearPow (0 : FpPoly p) (m + 1) = 0 := by
    intro m
    induction m with
    | zero =>
        rw [FpPoly.linearPow_succ]
        exact FpPoly.one_mul 0
    | succ m ih =>
        rw [FpPoly.linearPow_succ, ih, FpPoly.zero_mul]
  cases n with
  | zero => omega
  | succ n => exact hsucc n

omit [ZMod64.PrimeModulus p] in
private theorem linearPow_one (n : Nat) :
    FpPoly.linearPow (1 : FpPoly p) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FpPoly.linearPow_succ, ih, FpPoly.one_mul]

private theorem dvd_linearPow_sub_self_of_congr_zero
    (a h : FpPoly p) (hcongr : DensePoly.Congr h 0 a) :
    a ∣ (FpPoly.linearPow h p - h) := by
  have hp_pos : 0 < p := by
    have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
    omega
  have hpow :
      DensePoly.Congr (FpPoly.linearPow h p)
        (FpPoly.linearPow (0 : FpPoly p) p) a :=
    linearPow_congr_of_congr a h 0 p hcongr
  have hdiff :
      DensePoly.Congr (FpPoly.linearPow h p - h)
        (FpPoly.linearPow (0 : FpPoly p) p - (0 : FpPoly p)) a :=
    congr_sub_of_congr a _ _ _ _ hpow hcongr
  rw [linearPow_zero_of_pos p hp_pos, FpPoly.sub_zero] at hdiff
  change a ∣ (FpPoly.linearPow h p - h) - 0 at hdiff
  rwa [FpPoly.sub_zero] at hdiff

private theorem dvd_linearPow_sub_self_of_congr_one
    (b h : FpPoly p) (hcongr : DensePoly.Congr h 1 b) :
    b ∣ (FpPoly.linearPow h p - h) := by
  have hpow :
      DensePoly.Congr (FpPoly.linearPow h p)
        (FpPoly.linearPow (1 : FpPoly p) p) b :=
    linearPow_congr_of_congr b h 1 p hcongr
  have hdiff :
      DensePoly.Congr (FpPoly.linearPow h p - h)
        (FpPoly.linearPow (1 : FpPoly p) p - (1 : FpPoly p)) b :=
    congr_sub_of_congr b _ _ _ _ hpow hcongr
  rw [linearPow_one p, FpPoly.sub_self] at hdiff
  change b ∣ (FpPoly.linearPow h p - h) - 0 at hdiff
  rwa [FpPoly.sub_zero] at hdiff

private theorem mul_dvd_of_dvd_dvd_common
    {a b q : FpPoly p}
    (haq : a ∣ q) (hbq : b ∣ q)
    (hcommon : ∀ d : FpPoly p, d ∣ a → d ∣ b → d ∣ (1 : FpPoly p)) :
    a * b ∣ q := by
  rcases hbq with ⟨r, hr⟩
  have ha_dvd_br : a ∣ b * r := by
    rw [← hr]
    exact haq
  have ha_dvd_r : a ∣ r :=
    FpPoly.dvd_of_dvd_mul_of_common_dvd_one ha_dvd_br
      (fun d hdb hda => hcommon d hda hdb)
  rcases ha_dvd_r with ⟨s, hs⟩
  refine ⟨s, ?_⟩
  calc
    q = b * r := hr
    _ = b * (a * s) := by rw [hs]
    _ = (b * a) * s := (FpPoly.mul_assoc b a s).symm
    _ = (a * b) * s := by rw [FpPoly.mul_comm b a]

private theorem not_congr_constant_mod_of_mod
    (f h : FpPoly p) (c : ZMod64 p)
    (hnot : ¬ DensePoly.Congr h (DensePoly.C c) f) :
    ¬ DensePoly.Congr (h % f) (DensePoly.C c) f := by
  intro hconst
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hconst_mod :
      (h % f) % f = (DensePoly.C c : FpPoly p) % f :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) inferInstance inferInstance
      inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ _ hconst
  have hbase_mod : h % f = (h % f) % f := (DensePoly.mod_mod h f).symm
  apply hnot
  apply @DensePoly.congr_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
    inferInstance (ZMod64.instDivModLawsZMod64Fp p)
  exact hbase_mod.trans hconst_mod

/--
Reduced zero-one CRT witness for a monic coprime product split.  The witness is
Frobenius-fixed modulo `a * b` and is not congruent to any field constant
modulo that product.
-/
theorem exists_reduced_crtZeroOne_kernelWitness_of_coprime_split
    (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hgcd : DensePoly.gcd a b = 1) :
    ∃ h : FpPoly p,
      h = crtZeroOneXGCDCandidate a b % (a * b) ∧
      (a * b) ∣ (FpPoly.linearPow h (p ^ 1) - h) ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b) := by
  let h0 := crtZeroOneXGCDCandidate a b
  refine ⟨h0 % (a * b), rfl, ?_, ?_⟩
  · have hleft : a ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_zero a h0
        (crtZeroOneXGCDCandidate_congr_zero_left a b hgcd)
    have hright : b ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_one b h0
        (crtZeroOneXGCDCandidate_congr_one_right a b hgcd)
    have hprod : a * b ∣ (FpPoly.linearPow h0 p - h0) :=
      mul_dvd_of_dvd_dvd_common hleft hright
        (fun d hda hdb =>
          by
            rw [← hgcd]
            exact DensePoly.dvd_gcd d a b hda hdb)
    have hred :=
      (dvd_linearPow_sub_self_mod_iff (a * b) h0 1).mp
        (by simpa using hprod)
    simpa using hred
  · intro c
    apply not_congr_constant_mod_of_mod (a * b) h0 c
    exact crtZeroOneXGCDCandidate_not_congr_constant_mod_product
      a b ha hb ha_pos hb_pos hgcd c

/--
Trivial case for `deg f = 0`: `frobeniusDiffMod` is already its own
canonical remainder modulo `f`. When `deg f = 0` and `f` is monic, `f`
must have size 1 (since `Monic 0` is impossible over a prime field), and
every polynomial mod a degree-0 monic divisor is `0`; `frobeniusDiffMod`
is no exception, so both sides reduce to `0`.
-/
theorem frobeniusDiffMod_mod_self_of_degree_zero
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat)
    (hdeg : ¬ 0 < f.degree?.getD 0) :
    (frobeniusDiffMod f hmonic k) % f = frobeniusDiffMod f hmonic k := by
  -- f.size ≥ 1 (Monic excludes f = 0).
  have hf_size_pos : 0 < f.size := by
    apply Nat.pos_of_ne_zero
    intro hfsize
    have hfzero : f = 0 := by
      apply DensePoly.ext_coeff
      intro i; rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le f (by omega)
    rw [hfzero] at hmonic
    have h0lead : (0 : FpPoly p).leadingCoeff = 0 := by
      change (0 : FpPoly p).coeffs.back?.getD 0 = 0
      have hcoeffs : (0 : FpPoly p).coeffs = #[] := rfl
      rw [hcoeffs]; rfl
    unfold DensePoly.Monic at hmonic
    rw [h0lead] at hmonic
    -- hmonic : (0 : ZMod64 p) = 1, contradiction in a prime field.
    have h2 : 2 ≤ p := Hex.Nat.Prime.two_le ZMod64.PrimeModulus.prime
    have htoNat0 : (0 : ZMod64 p).toNat = 0 := ZMod64.toNat_zero
    have htoNat1 : (1 : ZMod64 p).toNat = 1 := by
      change (ZMod64.natCast p 1).toNat = 1
      rw [ZMod64.toNat_natCast]
      exact Nat.one_mod_eq_one.mpr (by omega)
    have htoNat : (0 : ZMod64 p).toNat = (1 : ZMod64 p).toNat :=
      congrArg ZMod64.toNat hmonic
    rw [htoNat0, htoNat1] at htoNat
    omega
  -- f.size = 1.
  have hf_size : f.size = 1 := by
    unfold DensePoly.degree? at hdeg
    have hne : f.size ≠ 0 := Nat.pos_iff_ne_zero.mp hf_size_pos
    simp [hne] at hdeg
    omega
  -- The cancellation property holds: a - (a / 1) * 1 = a - a = 0.
  have hcancel :
      ∀ a : ZMod64 p, a - (a / f.leadingCoeff) * f.leadingCoeff = (Zero.zero : ZMod64 p) := by
    intro a
    have hlead : f.leadingCoeff = (1 : ZMod64 p) := hmonic
    rw [hlead]
    have ha_div : a / (1 : ZMod64 p) = a := ZMod64.zmod_div_one a
    rw [ha_div]
    show a - a * 1 = (Zero.zero : ZMod64 p)
    have h_a_mul_one : a * (1 : ZMod64 p) = a := Lean.Grind.Semiring.mul_one a
    rw [h_a_mul_one]
    show a - a = (Zero.zero : ZMod64 p)
    have hzero_eq : (Zero.zero : ZMod64 p) = 0 := rfl
    rw [hzero_eq]
    grind
  -- For any p, p % f = 0 (since f has size 1 and the cancellation holds).
  have hmod_zero : ∀ q : FpPoly p, q % f = 0 := by
    intro q
    show (DensePoly.divMod q f).2 = 0
    exact DensePoly.divMod_remainder_eq_zero_of_degree_zero_core q f hf_size hcancel
  -- Show frobeniusDiffMod = 0.
  have hfrob_zero : FpPoly.frobeniusXPowMod f hmonic k = 0 := by
    have h := hmod_zero (FpPoly.frobeniusXPowMod f hmonic k)
    rw [FpPoly.frobeniusXPowMod_mod_self] at h
    exact h
  have hX_zero : FpPoly.modByMonic f FpPoly.X hmonic = 0 := by
    rw [show FpPoly.modByMonic f FpPoly.X hmonic = FpPoly.X % f from
          DensePoly.modByMonic_eq_mod _ _ hmonic]
    exact hmod_zero _
  have hdiff_zero : frobeniusDiffMod f hmonic k = 0 := by
    unfold frobeniusDiffMod
    rw [hfrob_zero, hX_zero, FpPoly.sub_self]
  rw [hdiff_zero, hmod_zero]

/--
`f` divides `X^(p^k) - X` (in the absolute sense) exactly when the
Berlekamp Frobenius remainder `frobeniusDiffMod f hmonic k` vanishes.

Identifies the absolute polynomial `xPowSubX k` with the modular Frobenius
remainder used by the executable `rabinTest`. The proof goes through
`frobeniusDiffMod = (xPowSubX k) % f`, which itself relies on
`frobeniusXPowMod_eq_powMod` for the absolute Frobenius identity.
-/
theorem dvd_xPowSubX_iff_frobeniusDiffMod_isZero
    (f : FpPoly p) (hmonic : DensePoly.Monic f) (k : Nat) :
    f ∣ xPowSubX (p := p) k ↔ (frobeniusDiffMod f hmonic k).isZero = true := by
  have inst_dvd : DensePoly.DivModLaws (ZMod64 p) := inferInstance
  -- Helper 1: f ∣ q ↔ q % f = 0.
  have hdvd_iff_mod : ∀ q : FpPoly p, f ∣ q ↔ q % f = 0 := fun q => by
    refine ⟨DensePoly.mod_eq_zero_of_dvd q f, ?_⟩
    intro hmod
    refine ⟨q / f, ?_⟩
    have h := DensePoly.div_mul_add_mod q f
    rw [hmod, FpPoly.add_zero, FpPoly.mul_comm] at h
    exact h.symm
  -- Helper 2: q.isZero = true ↔ q = 0.
  have hisZero_iff_eq : ∀ q : FpPoly p, q.isZero = true ↔ q = 0 := fun q => by
    refine ⟨?_, ?_⟩
    · intro h
      apply DensePoly.ext_coeff
      intro i
      have hsize : q.size = 0 := by
        simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using h
      rw [DensePoly.coeff_zero]
      exact DensePoly.coeff_eq_zero_of_size_le q (by omega)
    · intro h
      subst h
      rfl
  -- Step 1: f ∣ ((xPowSubX k) - frobeniusDiffMod).
  have hdvd_diff : f ∣ (xPowSubX (p := p) k - frobeniusDiffMod f hmonic k) := by
    have hp1 : f ∣ ((DensePoly.monomial (p^k) (1 : ZMod64 p)) -
                    FpPoly.frobeniusXPowMod f hmonic k) :=
      @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _
        (FpPoly.frobeniusXPowMod_mod_eq_monomial_mod f hmonic k).symm
    have hp2 : f ∣ (FpPoly.X - FpPoly.modByMonic f FpPoly.X hmonic) := by
      rw [show FpPoly.modByMonic f FpPoly.X hmonic = FpPoly.X % f from
            DensePoly.modByMonic_eq_mod _ _ hmonic]
      have hmm : (FpPoly.X (p := p)) % f = (FpPoly.X (p := p) % f) % f :=
        (DensePoly.mod_mod FpPoly.X f).symm
      exact @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _ hmm
    have heq :
        xPowSubX (p := p) k - frobeniusDiffMod f hmonic k =
          ((DensePoly.monomial (p^k) (1 : ZMod64 p)) -
              FpPoly.frobeniusXPowMod f hmonic k) -
            (FpPoly.X - FpPoly.modByMonic f FpPoly.X hmonic) := by
      unfold xPowSubX frobeniusDiffMod
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring]
      grind
    rw [heq]
    exact DensePoly.dvd_sub_poly hp1 hp2
  -- Step 2: (xPowSubX k) % f = (frobeniusDiffMod) % f.
  have hmodeq : (xPowSubX (p := p) k) % f = (frobeniusDiffMod f hmonic k) % f :=
    @DensePoly.mod_eq_mod_of_congr (ZMod64 p) _ _ _ inst_dvd _ _ _ hdvd_diff
  -- Step 3: frobeniusDiffMod % f = frobeniusDiffMod.
  -- Two cases: 0 < deg f or deg f = 0 (so f = 1, frobeniusDiffMod = 0).
  have hreduced : (frobeniusDiffMod f hmonic k) % f = frobeniusDiffMod f hmonic k := by
    by_cases hdeg : 0 < f.degree?.getD 0
    · -- 0 < deg f: show frobeniusDiffMod is reduced via coefficient bound.
      apply DensePoly.mod_eq_self_of_degree_lt
      -- Need: (frobeniusDiffMod).degree?.getD 0 < f.degree?.getD 0.
      -- Both frobeniusXPowMod and modByMonic f X hmonic have degree < f.degree.
      have hfrob_deg : (FpPoly.frobeniusXPowMod f hmonic k).degree?.getD 0 <
          f.degree?.getD 0 := by
        rw [← FpPoly.frobeniusXPowMod_mod_self f hmonic k]
        exact DensePoly.mod_degree_lt_of_pos_degree _ _ hdeg
      have hX_deg : (FpPoly.modByMonic f FpPoly.X hmonic).degree?.getD 0 <
          f.degree?.getD 0 := by
        rw [show FpPoly.modByMonic f FpPoly.X hmonic = FpPoly.X % f from
              DensePoly.modByMonic_eq_mod _ _ hmonic]
        exact DensePoly.mod_degree_lt_of_pos_degree _ _ hdeg
      -- Coefficient bound: for i ≥ f.size, (frobeniusDiffMod).coeff i = 0.
      have hf_size_pos : 0 < f.size := by
        apply Nat.pos_of_ne_zero
        intro hfsize
        unfold DensePoly.degree? at hdeg
        simp [hfsize] at hdeg
      have hf_deg_eq : f.degree?.getD 0 = f.size - 1 := by
        unfold DensePoly.degree?
        simp [Nat.ne_of_gt hf_size_pos]
      -- Convert hfrob_deg to a size bound.
      have hfrob_size : (FpPoly.frobeniusXPowMod f hmonic k).size ≤ f.size - 1 := by
        rw [hf_deg_eq] at hfrob_deg
        by_cases hsize : (FpPoly.frobeniusXPowMod f hmonic k).size = 0
        · omega
        · have hdeg' :
              (FpPoly.frobeniusXPowMod f hmonic k).degree?.getD 0 =
                (FpPoly.frobeniusXPowMod f hmonic k).size - 1 := by
            unfold DensePoly.degree?; simp [hsize]
          rw [hdeg'] at hfrob_deg
          omega
      have hX_size : (FpPoly.modByMonic f FpPoly.X hmonic).size ≤ f.size - 1 := by
        rw [hf_deg_eq] at hX_deg
        by_cases hsize : (FpPoly.modByMonic f FpPoly.X hmonic).size = 0
        · omega
        · have hdeg' :
              (FpPoly.modByMonic f FpPoly.X hmonic).degree?.getD 0 =
                (FpPoly.modByMonic f FpPoly.X hmonic).size - 1 := by
            unfold DensePoly.degree?; simp [hsize]
          rw [hdeg'] at hX_deg
          omega
      have hcoeff_zero :
          ∀ i, f.size - 1 ≤ i → (frobeniusDiffMod f hmonic k).coeff i = 0 := by
        intro i hi
        unfold frobeniusDiffMod
        rw [DensePoly.coeff_sub_ring]
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega : _ ≤ i)]
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega : _ ≤ i)]
        grind
      -- Conclude: (frobeniusDiffMod).size ≤ f.size - 1.
      have hdiff_size : (frobeniusDiffMod f hmonic k).size ≤ f.size - 1 := by
        rcases Nat.lt_or_ge (f.size - 1) (frobeniusDiffMod f hmonic k).size with hcontra | hle
        · exfalso
          have hi : f.size - 1 ≤ (frobeniusDiffMod f hmonic k).size - 1 := by omega
          have hc :=
            DensePoly.coeff_last_ne_zero_of_pos_size (frobeniusDiffMod f hmonic k)
              (by omega)
          exact hc (hcoeff_zero _ hi)
        · exact hle
      -- Translate back to degree.
      by_cases hsize : (frobeniusDiffMod f hmonic k).size = 0
      · -- frobeniusDiffMod = 0 case: degree = 0 < f.degree.
        have hdeg_zero :
            (frobeniusDiffMod f hmonic k).degree?.getD 0 = 0 := by
          unfold DensePoly.degree?
          simp [hsize]
        rw [hdeg_zero]
        exact hdeg
      · -- size > 0: degree = size - 1 ≤ f.size - 2 < f.size - 1 = f.degree.
        have hdeg_eq :
            (frobeniusDiffMod f hmonic k).degree?.getD 0 =
              (frobeniusDiffMod f hmonic k).size - 1 := by
          unfold DensePoly.degree?
          simp [hsize]
        rw [hdeg_eq, hf_deg_eq]
        omega
    · -- deg f = 0. We use the absolute identity: f = monomial 0 1 (since Monic + size 1).
      -- This case is the trivial one where f is the constant polynomial 1.
      -- Discharged via the `f = 1` lemma, which is itself a clean foundational fact.
      exact frobeniusDiffMod_mod_self_of_degree_zero f hmonic k hdeg
  -- Chain: f ∣ xPowSubX k ↔ (xPowSubX k) % f = 0 ↔ frobeniusDiffMod % f = 0
  --                       ↔ frobeniusDiffMod = 0 ↔ isZero = true.
  rw [hdvd_iff_mod, hmodeq, hreduced, hisZero_iff_eq]

/--
The executable divisibility leg of Rabin's test is exactly the absolute
condition `f ∣ X^(p^n) - X`, where `n = basisSize f`.

This is the caller-facing form of
`dvd_xPowSubX_iff_frobeniusDiffMod_isZero` for code that consumes
`rabinDividesTest` without unfolding `frobeniusDiffMod`.
-/
theorem rabinDividesTest_eq_true_iff_dvd_xPowSubX
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    rabinDividesTest f hmonic = true ↔
      f ∣ xPowSubX (p := p) (basisSize f) := by
  unfold rabinDividesTest
  exact (dvd_xPowSubX_iff_frobeniusDiffMod_isZero f hmonic (basisSize f)).symm

/--
Boolean characterization of the executable Rabin test in theorem-facing
terms: positive degree, absolute divisibility by `X^(p^n) - X`, and all
maximal-proper-divisor gcd witnesses accepted.
-/
theorem rabinTest_eq_true_iff
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    rabinTest f hmonic = true ↔
      0 < basisSize f ∧
        f ∣ xPowSubX (p := p) (basisSize f) ∧
        (rabinWitnesses f hmonic).all Prod.snd = true := by
  unfold rabinTest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.1.1, (rabinDividesTest_eq_true_iff_dvd_xPowSubX f hmonic).mp h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, (rabinDividesTest_eq_true_iff_dvd_xPowSubX f hmonic).mpr h.2.1⟩,
      h.2.2⟩

omit [ZMod64.PrimeModulus p] in
/--
A polynomial of positive degree is nonzero.

Used to discharge the `f ≠ 0` leg of `FpPoly.Irreducible` and to show
that the factors `a, b` of `f` are individually nonzero.
-/
theorem ne_zero_of_pos_degree
    {f : FpPoly p} (hpos : 0 < f.degree?.getD 0) :
    f ≠ 0 := by
  intro hzero
  rw [hzero] at hpos
  unfold DensePoly.degree? at hpos
  simp at hpos

omit [ZMod64.PrimeModulus p] in
private theorem zmod64_one_ne_zero_local [ZMod64.PrimeModulus p] :
    (1 : ZMod64 p) ≠ (0 : ZMod64 p) := by
  intro h
  have h2 : 2 ≤ p := Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  exact absurd htoNat (by omega)

omit [ZMod64.PrimeModulus p] in
private theorem inv_leadingCoeff_ne_zero_of_pos_degree [ZMod64.PrimeModulus p]
    (a : FpPoly p) (ha_pos : 0 < a.degree?.getD 0) :
    (DensePoly.leadingCoeff a)⁻¹ ≠ (0 : ZMod64 p) := by
  intro hinv
  have hlead_ne := FpPoly.leadingCoeff_ne_zero_of_pos_degree a ha_pos
  change ZMod64.inv (DensePoly.leadingCoeff a) = (0 : ZMod64 p) at hinv
  have hone := ZMod64.inv_mul_eq_one_of_prime
    (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
  rw [hinv] at hone
  have hzero : (0 : ZMod64 p) * DensePoly.leadingCoeff a = 0 := by grind
  rw [hzero] at hone
  exact zmod64_one_ne_zero_local hone.symm

omit [ZMod64.PrimeModulus p] in
private theorem factor_ne_zero_of_ne_zero_local
    {f a b : FpPoly p} (hab : a * b = f) (hf_ne_zero : f ≠ 0) :
    a ≠ 0 := by
  intro hzero
  rw [hzero, FpPoly.zero_mul] at hab
  exact hf_ne_zero hab.symm

omit [ZMod64.PrimeModulus p] in
private theorem pos_degree_of_ne_zero_of_not_isUnit_local
    {a : FpPoly p} (ha_ne_zero : a ≠ 0)
    (ha_not_unit : a.degree? ≠ some 0) :
    0 < a.degree?.getD 0 := by
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha_ne_zero
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  have hdeg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  rw [hdeg] at ha_not_unit
  rw [hdeg]
  have : a.size - 1 ≠ 0 := fun h => ha_not_unit (by rw [h])
  simp
  omega

omit [ZMod64.PrimeModulus p] in
private theorem fp_dvd_trans_local {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, FpPoly.mul_assoc]

private theorem factor_degree_lt
    {a x y : FpPoly p}
    (hxy : x * y = a) (hx_ne_zero : x ≠ 0)
    (hy_pos : 0 < y.degree?.getD 0) :
    x.degree?.getD 0 < a.degree?.getD 0 := by
  have hy_ne_zero : y ≠ 0 := ne_zero_of_pos_degree hy_pos
  rw [← hxy]
  rw [FpPoly.degree?_mul_eq_add_degree? x y hx_ne_zero hy_ne_zero]
  omega

private theorem exists_monic_irreducible_factor_of_pos_degree_aux :
    ∀ (n : Nat) (a : FpPoly p), a.degree?.getD 0 = n →
        0 < a.degree?.getD 0 →
        ∃ g : FpPoly p,
          FpPoly.Irreducible g ∧ DensePoly.Monic g ∧ g ∣ a ∧
            0 < g.degree?.getD 0 ∧ g.degree?.getD 0 ≤ a.degree?.getD 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a hn ha_pos
    by_cases hirr : FpPoly.Irreducible a
    · let c : ZMod64 p := (DensePoly.leadingCoeff a)⁻¹
      have hc : c ≠ 0 := inv_leadingCoeff_ne_zero_of_pos_degree a ha_pos
      refine ⟨DensePoly.scale c a, ?_, ?_, ?_, ?_, ?_⟩
      · exact FpPoly.irreducible_scale_of_ne_zero (p := p) hc hirr
      · exact FpPoly.scale_inv_leadingCoeff_monic a ha_pos
      · exact FpPoly.dvd_scale_self_of_ne_zero (p := p) hc a
      · rw [FpPoly.scale_degree?_getD_eq_of_ne_zero (p := p) hc a]
        exact ha_pos
      · rw [FpPoly.scale_degree?_getD_eq_of_ne_zero (p := p) hc a]
        exact Nat.le_refl _
    · have ha_ne : a ≠ 0 := ne_zero_of_pos_degree ha_pos
      have hnotforall :
          ¬ (∀ x y : FpPoly p, x * y = a →
              x.degree? = some 0 ∨ y.degree? = some 0) :=
        fun h => hirr ⟨ha_ne, h⟩
      have hex :
          ∃ x y : FpPoly p,
            x * y = a ∧ x.degree? ≠ some 0 ∧ y.degree? ≠ some 0 := by
        apply Classical.byContradiction
        intro hno
        apply hnotforall
        intro x y hxy
        by_cases hx0 : x.degree? = some 0
        · exact Or.inl hx0
        · by_cases hy0 : y.degree? = some 0
          · exact Or.inr hy0
          · exact (hno ⟨x, y, hxy, hx0, hy0⟩).elim
      obtain ⟨x, y, hxy, hx_not_unit, hy_not_unit⟩ := hex
      have hx_ne_zero : x ≠ 0 := factor_ne_zero_of_ne_zero_local hxy ha_ne
      have hy_ne_zero : y ≠ 0 := by
        have hyx : y * x = a := by rw [FpPoly.mul_comm]; exact hxy
        exact factor_ne_zero_of_ne_zero_local hyx ha_ne
      have hx_pos : 0 < x.degree?.getD 0 :=
        pos_degree_of_ne_zero_of_not_isUnit_local hx_ne_zero hx_not_unit
      have hy_pos : 0 < y.degree?.getD 0 :=
        pos_degree_of_ne_zero_of_not_isUnit_local hy_ne_zero hy_not_unit
      have hx_dvd_a : x ∣ a := ⟨y, hxy.symm⟩
      have hx_lt : x.degree?.getD 0 < a.degree?.getD 0 :=
        factor_degree_lt hxy hx_ne_zero hy_pos
      have hx_lt_n : x.degree?.getD 0 < n := hn ▸ hx_lt
      obtain ⟨g, hg_irr, hg_monic, hg_dvd_x, hg_deg_pos, hg_deg_le_x⟩ :=
        ih (x.degree?.getD 0) hx_lt_n x rfl hx_pos
      exact ⟨g, hg_irr, hg_monic, fp_dvd_trans_local hg_dvd_x hx_dvd_a, hg_deg_pos,
        Nat.le_trans hg_deg_le_x (Nat.le_of_lt hx_lt)⟩

/--
Existence of a monic irreducible factor for any non-unit factor.

For a polynomial `a : FpPoly p` of positive degree appearing as a factor
of a monic polynomial `f`, there is a monic irreducible `g ∣ a` with
`0 < deg g ≤ deg a`. Standard descent on degree, with the monic-associate
rescaling needed when `a` itself is not monic.
-/
theorem exists_monic_irreducible_factor_of_factor
    {f a b : FpPoly p}
    (_hmonic_f : DensePoly.Monic f) (_hab : a * b = f)
    (ha_pos : 0 < a.degree?.getD 0) :
    ∃ g : FpPoly p,
      FpPoly.Irreducible g ∧ DensePoly.Monic g ∧ g ∣ a ∧
        0 < g.degree?.getD 0 ∧ g.degree?.getD 0 ≤ a.degree?.getD 0 := by
  exact exists_monic_irreducible_factor_of_pos_degree_aux (a.degree?.getD 0) a rfl ha_pos

/--
The quotient class of `X` raised to `p^k` is represented by the executable
Frobenius remainder `frobeniusXPowMod`.
-/
theorem quotient_X_pow_eq_reduce_frobeniusXPowMod
    {g : FpPoly p} (hg_monic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) (k : Nat) :
    (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) ^ (p ^ k) =
      FpPoly.Quotient.reduce
        (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
        (FpPoly.frobeniusXPowMod g hg_monic k) := by
  calc
    (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) ^ (p ^ k) =
        FpPoly.Quotient.reduce
          (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
          (FpPoly.linearPow FpPoly.X (p ^ k)) := by
          exact (FpPoly.Quotient.reduce_linearPow_eq_pow
            (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
            FpPoly.X (p ^ k)).symm
    _ =
        FpPoly.Quotient.reduce
          (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
          (DensePoly.monomial (p ^ k) (1 : ZMod64 p)) := by
          change
            FpPoly.Quotient.reduce
              (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
              (FpPoly.linearPow (DensePoly.monomial 1 (1 : ZMod64 p)) (p ^ k)) =
            FpPoly.Quotient.reduce
              (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
              (DensePoly.monomial (p ^ k) (1 : ZMod64 p))
          rw [FpPoly.linearPow_monomial_one]
    _ =
        FpPoly.Quotient.reduce
          (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
          (FpPoly.frobeniusXPowMod g hg_monic k) := by
          apply FpPoly.Quotient.reduce_eq_reduce_of_congr
          unfold FpPoly.Quotient.Congr
          letI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
          exact @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) inferInstance inferInstance
            inferInstance (ZMod64.instDivModLawsZMod64Fp p) _ _ g
            (FpPoly.frobeniusXPowMod_mod_eq_monomial_mod g hg_monic k).symm

/--
Rabin's degree-divisibility theorem in its `FpPoly` form (forward
direction).

If `g` is a monic irreducible polynomial of degree `d > 0` over `F_p` and
`g ∣ X^(p^n) - X`, then `d ∣ n`. The standard proof works in the residue
field `F_p[X]/(g)` and shows that `X` has multiplicative order dividing
`p^d - 1`, forcing `d ∣ n` via the order of the Frobenius automorphism.

This is the deepest finite-field ingredient of Rabin's test soundness.
-/
theorem degree_dvd_of_irreducible_dvd_xPowSubX
    {g : FpPoly p} (hg_irr : FpPoly.Irreducible g)
    (hg_monic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) {n : Nat}
    (hg_dvd : g ∣ xPowSubX (p := p) n) :
    g.degree?.getD 0 ∣ n := by
  letI inst_dvd : DensePoly.DivModLaws (ZMod64 p) := inferInstance
  have hX :
      (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) ^
          (p ^ n) =
        FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) := by
    calc
      (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) ^
          (p ^ n) =
          FpPoly.Quotient.reduce
            (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
            (FpPoly.frobeniusXPowMod g hg_monic n) := by
            exact quotient_X_pow_eq_reduce_frobeniusXPowMod hg_monic hg_pos n
      _ =
          FpPoly.Quotient.reduce
            (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)
            (DensePoly.monomial (p ^ n) (1 : ZMod64 p)) := by
            apply FpPoly.Quotient.reduce_eq_reduce_of_congr
            unfold FpPoly.Quotient.Congr
            exact @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _
              (FpPoly.frobeniusXPowMod_mod_eq_monomial_mod g hg_monic n)
      _ =
          FpPoly.Quotient.reduce
            (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) FpPoly.X := by
            apply FpPoly.Quotient.reduce_eq_reduce_of_congr
            unfold FpPoly.Quotient.Congr
            exact hg_dvd
      _ =
          FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) := rfl
  have huniversal :
      ∀ β : FpPoly.Quotient g hg_monic hg_pos, β ^ (p ^ n) = β :=
    FpPoly.Quotient.pow_pPowN_eq_self_of_pow_pPowN_X_eq_X hg_irr hX
  exact FpPoly.Quotient.deg_dvd_of_pow_pPowN_eq_self_universal
    (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) hg_irr huniversal

/--
Rabin's degree-divisibility theorem in its `FpPoly` form (backward
direction).

A monic irreducible polynomial `g` of degree `d > 0` over `F_p` divides
`X^(p^d) - X`. The standard proof builds the residue field
`F_p[X]/(g)` of order `p^d` and applies the Frobenius identity
`α^(p^d) = α` for every element of a finite field of order `p^d`.
-/
theorem irreducible_dvd_xPowSubX_degree
    {g : FpPoly p} (hg_irr : FpPoly.Irreducible g)
    (hg_monic : DensePoly.Monic g)
    (hg_pos : 0 < g.degree?.getD 0) :
    g ∣ xPowSubX (p := p) (g.degree?.getD 0) := by
  letI inst_dvd : DensePoly.DivModLaws (ZMod64 p) := inferInstance
  -- Step 1: the quotient class of `X` is fixed by raising to `p ^ d`.
  have hfix :
      (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) ^
          (p ^ g.degree?.getD 0) =
        FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) :=
    FpPoly.Quotient.pow_card_eq_self_of_irreducible hg_irr _
  -- Step 2: rewrite the LHS to the executable representative.
  rw [quotient_X_pow_eq_reduce_frobeniusXPowMod hg_monic hg_pos
      (g.degree?.getD 0)] at hfix
  -- `Quotient.X = reduce X` is definitional.
  have hX_def :
      (FpPoly.Quotient.X (g := g) (hmonic := hg_monic) (hg_pos := hg_pos)) =
        FpPoly.Quotient.reduce
          (g := g) (hmonic := hg_monic) (hg_pos := hg_pos) FpPoly.X := rfl
  rw [hX_def] at hfix
  -- Step 3: extract the polynomial congruence `g ∣ frobeniusXPowMod - X`.
  have hcongr :
      g ∣ (FpPoly.frobeniusXPowMod g hg_monic (g.degree?.getD 0) - FpPoly.X) :=
    FpPoly.Quotient.congr_of_reduce_eq_reduce hfix
  -- Step 4: the absolute Frobenius identity, `g ∣ X^(p^d) - frobeniusXPowMod`.
  have hp1 :
      g ∣ ((DensePoly.monomial (p ^ g.degree?.getD 0) (1 : ZMod64 p)) -
            FpPoly.frobeniusXPowMod g hg_monic (g.degree?.getD 0)) :=
    @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _
      (FpPoly.frobeniusXPowMod_mod_eq_monomial_mod g hg_monic
        (g.degree?.getD 0)).symm
  -- Step 5: rewrite `xPowSubX d` as the sum of the two divisible pieces.
  have heq :
      (xPowSubX (p := p) (g.degree?.getD 0)) =
        ((DensePoly.monomial (p ^ g.degree?.getD 0) (1 : ZMod64 p)) -
            FpPoly.frobeniusXPowMod g hg_monic (g.degree?.getD 0)) +
          (FpPoly.frobeniusXPowMod g hg_monic (g.degree?.getD 0) - FpPoly.X) := by
    unfold xPowSubX
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_sub_ring,
        DensePoly.coeff_add_semiring,
        DensePoly.coeff_sub_ring,
        DensePoly.coeff_sub_ring]
    grind
  rw [heq]
  exact DensePoly.dvd_add_poly hp1 hcongr

/--
Divisibility chain on Rabin polynomials: if `d ∣ m`, then
`X^(p^d) - X` divides `X^(p^m) - X` inside `FpPoly p`.

A standard polynomial-algebra identity. Used to lift divisibility of an
irreducible factor `g` from `X^(p^d) - X` to `X^(p^m) - X` where `m` is a
maximal proper divisor of `n` in which `d` lives.
-/
private theorem xPowSubX_factor (k : Nat) :
    xPowSubX (p := p) k =
      FpPoly.X * (DensePoly.monomial (p ^ k - 1) (1 : ZMod64 p) - 1) := by
  unfold xPowSubX FpPoly.X
  have hp_pos : 0 < p := by
    have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
    omega
  have hp_gt_one : 1 < p := by
    have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
    omega
  have hp_ne_one : p ≠ 1 := by omega
  have hpow_pos : 0 < p ^ k := Nat.pow_pos hp_pos
  have hcoeff_one :
      ∀ i, (1 : FpPoly p).coeff i = if i = 0 then (1 : ZMod64 p) else 0 := by
    intro i
    change (DensePoly.C (1 : ZMod64 p)).coeff i =
      if i = 0 then (1 : ZMod64 p) else 0
    exact DensePoly.coeff_C (1 : ZMod64 p) i
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring]
  rw [FpPoly.coeff_monomial_mul]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_monomial, hcoeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    have h0pow_ne : ¬ 0 = p ^ k := by omega
    simp [h0pow_ne]
    grind
  · have hn_not_lt : ¬ n < 1 := by omega
    simp [hn_not_lt]
    by_cases hnpow : n = p ^ k
    · by_cases hk0 : k = 0
      · simp [hnpow, hk0]
      · have hpow_gt_one : 1 < p ^ k := Nat.one_lt_pow hk0 hp_gt_one
        have hpow_sub_ne_zero : p ^ k - 1 ≠ 0 := by omega
        simp [hnpow, hp_ne_one, hk0, hpow_sub_ne_zero]
        change (1 : ZMod64 p) - (0 : ZMod64 p) = (1 : ZMod64 p) - (0 : ZMod64 p)
        rfl
    · have hsub_ne : n - 1 ≠ p ^ k - 1 := by omega
      by_cases hn1 : n = 1
      · subst hn1
        simp [hnpow, hsub_ne]
      · have hnsub0 : n - 1 ≠ 0 := by omega
        simp [hnpow, hsub_ne, hn1, hnsub0]
        change (0 : ZMod64 p) - (0 : ZMod64 p) = (0 : ZMod64 p) - (0 : ZMod64 p)
        rfl

theorem xPowSubX_dvd_of_dvd
    {d m : Nat} (_hdvd : d ∣ m) :
    xPowSubX (p := p) d ∣ xPowSubX (p := p) m := by
  have hpow_dvd :
      p ^ d - 1 ∣ p ^ m - 1 :=
    Hex.Nat.pow_sub_one_dvd_pow_sub_one_of_dvd p _hdvd
  have hgeo :
      ((DensePoly.monomial (p ^ d - 1) (1 : ZMod64 p) - 1) : FpPoly p) ∣
        (DensePoly.monomial (p ^ m - 1) (1 : ZMod64 p) - 1 : FpPoly p) :=
    FpPoly.monomial_sub_one_dvd_of_dvd hpow_dvd
  rw [xPowSubX_factor d, xPowSubX_factor m]
  rcases hgeo with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [hq, FpPoly.mul_assoc]

private theorem lt_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d < n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, hk, rfl⟩, _⟩
  omega

private theorem pos_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : 0 < d := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, _, rfl⟩, _⟩
  omega

private theorem dvd_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d ∣ n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, _, rfl⟩, hmod⟩
  exact Nat.dvd_of_mod_eq_zero hmod

private theorem mem_properDivisors_of_pos_of_dvd_of_lt {n d : Nat}
    (hpos : 0 < d) (hdvd : d ∣ n) (hlt : d < n) :
    d ∈ properDivisors n := by
  unfold properDivisors
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq]
  refine ⟨⟨d - 1, ?_, ?_⟩, ?_⟩
  · omega
  · omega
  · exact Nat.mod_eq_zero_of_dvd hdvd

private theorem exists_maximalProperDivisor_dvd_aux (n : Nat) :
    ∀ (k d : Nat), 0 < d → d ∣ n → d < n → n - d ≤ k →
        ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m
  | 0, _d, _hpos, _hdvd, hlt, hbound => by omega
  | k + 1, d, hpos, hdvd, hlt, hbound => by
      by_cases hmax : ∃ e, e ∈ properDivisors n ∧ d < e ∧ d ∣ e
      · obtain ⟨e, he_mem, he_lt, he_dvd⟩ := hmax
        have he_lt_n := lt_of_mem_properDivisors he_mem
        have he_dvd_n := dvd_of_mem_properDivisors he_mem
        have he_pos : 0 < e := Nat.lt_of_lt_of_le hpos (Nat.le_of_lt he_lt)
        have hsmaller : n - e ≤ k := by omega
        obtain ⟨m, hm_mem, hm_dvd⟩ :=
          exists_maximalProperDivisor_dvd_aux n k e he_pos he_dvd_n he_lt_n hsmaller
        exact ⟨m, hm_mem, Nat.dvd_trans he_dvd hm_dvd⟩
      · refine ⟨d, ?_, Nat.dvd_refl d⟩
        have hd_in : d ∈ properDivisors n :=
          mem_properDivisors_of_pos_of_dvd_of_lt hpos hdvd hlt
        unfold maximalProperDivisors
        simp only [List.mem_filter]
        refine ⟨hd_in, ?_⟩
        have hany_false :
            (properDivisors n).any
                (fun e => decide (d < e) && decide (e % d = 0)) = false := by
          apply Bool.eq_false_iff.mpr
          intro hany
          rw [List.any_eq_true] at hany
          obtain ⟨e, he_mem, he_cond⟩ := hany
          simp only [Bool.and_eq_true, decide_eq_true_eq] at he_cond
          exact hmax ⟨e, he_mem, he_cond.1, Nat.dvd_of_mod_eq_zero he_cond.2⟩
        rw [hany_false]
        rfl

/--
Every positive proper divisor `d` of `n` is dominated by some maximal
proper divisor of `n` (with `d` dividing it).

Combinatorial fact about the proper-divisor lattice. Used in the
contrapositive proof to route an irreducible factor's degree `d` to a
divisor at which the gcd leg of `rabinTest` rules out divisibility.
-/
theorem exists_maximalProperDivisor_dvd
    {n d : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m :=
  exists_maximalProperDivisor_dvd_aux n (n - d) d hd_pos hd_dvd hd_lt (Nat.le_refl _)

/--
A `g` that divides both `f` and `xPowSubX k` also divides the modular
Frobenius remainder `frobeniusDiffMod f hmonic k`.

Direct consequence of the absolute–modular Frobenius identity together
with the `divMod_spec` characterization of polynomial remainders.
-/
theorem dvd_frobeniusDiffMod_of_dvd_dvd
    {f g : FpPoly p} (hmonic : DensePoly.Monic f)
    (hg_dvd_f : g ∣ f) {k : Nat}
    (hg_dvd_pow : g ∣ xPowSubX (p := p) k) :
    g ∣ frobeniusDiffMod f hmonic k := by
  have inst_dvd : DensePoly.DivModLaws (ZMod64 p) := inferInstance
  -- Step 1: f ∣ ((xPowSubX k) - frobeniusDiffMod), reusing the algebra from the iff proof.
  have hdvd_diff : f ∣ (xPowSubX (p := p) k - frobeniusDiffMod f hmonic k) := by
    have hp1 : f ∣ ((DensePoly.monomial (p^k) (1 : ZMod64 p)) -
                    FpPoly.frobeniusXPowMod f hmonic k) :=
      @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _
        (FpPoly.frobeniusXPowMod_mod_eq_monomial_mod f hmonic k).symm
    have hp2 : f ∣ (FpPoly.X - FpPoly.modByMonic f FpPoly.X hmonic) := by
      rw [show FpPoly.modByMonic f FpPoly.X hmonic = FpPoly.X % f from
            DensePoly.modByMonic_eq_mod _ _ hmonic]
      have hmm : (FpPoly.X (p := p)) % f = (FpPoly.X (p := p) % f) % f :=
        (DensePoly.mod_mod FpPoly.X f).symm
      exact @DensePoly.dvd_of_mod_eq_mod (ZMod64 p) _ _ _ inst_dvd _ _ _ hmm
    have heq :
        xPowSubX (p := p) k - frobeniusDiffMod f hmonic k =
          ((DensePoly.monomial (p^k) (1 : ZMod64 p)) -
              FpPoly.frobeniusXPowMod f hmonic k) -
            (FpPoly.X - FpPoly.modByMonic f FpPoly.X hmonic) := by
      unfold xPowSubX frobeniusDiffMod
      apply DensePoly.ext_coeff
      intro n
      rw [DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring,
          DensePoly.coeff_sub_ring]
      grind
    rw [heq]
    exact DensePoly.dvd_sub_poly hp1 hp2
  -- Step 2: g ∣ (xPowSubX k - frobeniusDiffMod) since g ∣ f and f ∣ ...
  have hg_dvd_diff : g ∣ (xPowSubX (p := p) k - frobeniusDiffMod f hmonic k) := by
    rcases hdvd_diff with ⟨c, hc⟩
    rcases hg_dvd_f with ⟨d, hd⟩
    refine ⟨d * c, ?_⟩
    rw [hc, hd, FpPoly.mul_assoc]
  -- Step 3: g ∣ frobeniusDiffMod from g ∣ xPowSubX k and g ∣ (xPowSubX k - frobeniusDiffMod).
  -- Specifically, frobeniusDiffMod = xPowSubX k - (xPowSubX k - frobeniusDiffMod).
  have hgoal :
      frobeniusDiffMod f hmonic k =
        xPowSubX (p := p) k - (xPowSubX (p := p) k - frobeniusDiffMod f hmonic k) := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_sub_ring,
        DensePoly.coeff_sub_ring]
    grind
  rw [hgoal]
  exact DensePoly.dvd_sub_poly hg_dvd_pow hg_dvd_diff

/--
A divisor of a unit polynomial is itself a unit polynomial.

Routine consequence of degree arithmetic: if `g ∣ h` and `h` has degree 0
with nonzero constant, then `g` also has degree 0 with nonzero constant.
-/
theorem isUnitPolynomial_of_dvd_isUnitPolynomial
    {g h : FpPoly p} (hgh : g ∣ h) (hh : isUnitPolynomial h = true) :
    isUnitPolynomial g = true := by
  -- Translate `isUnitPolynomial h = true` into `h.degree? = some 0`.
  have hh_deg : h.degree? = some 0 := by
    unfold isUnitPolynomial at hh
    cases hdeg : h.degree? with
    | none => rw [hdeg] at hh; simp at hh
    | some k =>
      rw [hdeg] at hh
      cases k with
      | zero => rfl
      | succ _ => simp at hh
  have hh_ne_zero : h ≠ 0 := by
    intro heq
    rw [heq] at hh_deg
    unfold DensePoly.degree? at hh_deg
    simp at hh_deg
  rcases hgh with ⟨r, hr⟩
  have hg_ne_zero : g ≠ 0 := by
    intro hg
    apply hh_ne_zero
    rw [hr, hg, FpPoly.zero_mul]
  have hr_ne_zero : r ≠ 0 := by
    intro hzero
    apply hh_ne_zero
    rw [hr, hzero, FpPoly.mul_zero]
  -- `deg h = deg g + deg r` and `deg h = 0`, so `deg g = 0`.
  have hsum : h.degree?.getD 0 = g.degree?.getD 0 + r.degree?.getD 0 := by
    rw [hr]
    exact FpPoly.degree?_mul_eq_add_degree? g r hg_ne_zero hr_ne_zero
  have hh_deg_zero : h.degree?.getD 0 = 0 := by simp [hh_deg]
  have hg_deg_zero : g.degree?.getD 0 = 0 := by omega
  -- Translate `g ≠ 0 ∧ deg g = 0` back to `isUnitPolynomial g = true`.
  have hg_size_pos : 0 < g.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hg_ne_zero
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le g (by omega)
  have hg_size_ne_zero : g.size ≠ 0 := Nat.pos_iff_ne_zero.mp hg_size_pos
  have hg_deg : g.degree? = some (g.size - 1) := by
    unfold DensePoly.degree?
    simp [hg_size_ne_zero]
  rw [hg_deg] at hg_deg_zero
  simp at hg_deg_zero
  have hg_deg_some : g.degree? = some 0 := by
    rw [hg_deg, hg_deg_zero]
  unfold isUnitPolynomial
  rw [hg_deg_some]

omit [ZMod64.PrimeModulus p] in
/-- The factor `a` of a nontrivial product `a * b = f` is nonzero. -/
theorem factor_ne_zero_of_ne_zero
    {f a b : FpPoly p} (hab : a * b = f) (hf_ne_zero : f ≠ 0) :
    a ≠ 0 := by
  intro hzero
  rw [hzero, FpPoly.zero_mul] at hab
  exact hf_ne_zero hab.symm

omit [ZMod64.PrimeModulus p] in
/--
A nonzero polynomial whose `degree?` is not `some 0` has positive degree.
-/
theorem pos_degree_of_ne_zero_of_not_isUnit
    {a : FpPoly p} (ha_ne_zero : a ≠ 0)
    (ha_not_unit : a.degree? ≠ some 0) :
    0 < a.degree?.getD 0 := by
  -- Show `a.size > 0` from `a ≠ 0`.
  have ha_size_pos : 0 < a.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply ha_ne_zero
    apply DensePoly.ext_coeff
    intro i
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le a (by omega)
  have ha_size_ne_zero : a.size ≠ 0 := Nat.pos_iff_ne_zero.mp ha_size_pos
  -- Compute `a.degree? = some (a.size - 1)`.
  have hdeg : a.degree? = some (a.size - 1) := by
    unfold DensePoly.degree?
    simp [ha_size_ne_zero]
  rw [hdeg] at ha_not_unit
  rw [hdeg]
  -- `some (a.size - 1) ≠ some 0 ⟹ a.size - 1 ≠ 0 ⟹ 0 < a.size - 1`.
  have : a.size - 1 ≠ 0 := fun h => ha_not_unit (by rw [h])
  simp
  omega

/--
The degree of a factor `a` is strictly less than the degree of `f` whenever
the cofactor `b` has positive degree. Phrased relative to `basisSize` to
match the Berlekamp / Rabin scaffolding.
-/
theorem factor_degree_lt_basisSize
    {f a b : FpPoly p}
    (hab : a * b = f) (ha_ne_zero : a ≠ 0) (hb_pos : 0 < b.degree?.getD 0) :
    a.degree?.getD 0 < basisSize f := by
  have hb_ne_zero : b ≠ 0 := ne_zero_of_pos_degree hb_pos
  unfold basisSize
  rw [← hab]
  rw [FpPoly.degree?_mul_eq_add_degree? a b ha_ne_zero hb_ne_zero]
  omega

omit [ZMod64.PrimeModulus p] in
/--
The `m`-th maximal-proper-divisor witness of `rabinTest`: when the test
passes, every entry of `rabinWitnesses` is `true`, hence the gcd leg
holds at every maximal proper divisor.
-/
theorem rabinCoprimeTest_of_mem_maximalProperDivisors
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hwitnesses : (rabinWitnesses f hmonic).all Prod.snd = true)
    {m : Nat} (hm : m ∈ maximalProperDivisors (basisSize f)) :
    rabinCoprimeTest f hmonic m = true := by
  unfold rabinWitnesses at hwitnesses
  rw [List.all_eq_true] at hwitnesses
  have hmem :
      (m, rabinCoprimeTest f hmonic m) ∈
        (maximalProperDivisors (basisSize f)).map
          (fun d => (d, rabinCoprimeTest f hmonic d)) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  exact hwitnesses _ hmem

/-! ### Prime-field product identity -/

/-- Every prime-field residue is a root of `xPowSubX 1`: this is Fermat's
little theorem packaged through the executable `FpPoly` evaluation. -/
theorem xPowSubX_one_eval_eq_zero (c : ZMod64 p) :
    DensePoly.eval (xPowSubX (p := p) 1) c = 0 := by
  unfold xPowSubX
  rw [FpPoly.eval_sub, FpPoly.eval_monomial, FpPoly.eval_X]
  rw [Nat.pow_one, ZMod64.pow_prime_of_prime_modulus]
  grind

/-- Each prime-field linear factor `X - C c` divides `xPowSubX 1`. -/
theorem primeFieldLinearFactor_dvd_xPowSubX_one (c : ZMod64 p) :
    primeFieldLinearFactor c ∣ xPowSubX (p := p) 1 := by
  unfold primeFieldLinearFactor
  exact FpPoly.X_sub_C_dvd_of_eval_eq_zero (xPowSubX (p := p) 1) c
    (xPowSubX_one_eval_eq_zero c)

omit [ZMod64.PrimeModulus p] in
/-- The difference of two prime-field linear factors collapses to a constant. -/
private theorem primeFieldLinearFactor_sub_eq (c d : ZMod64 p) :
    primeFieldLinearFactor c - primeFieldLinearFactor d
      = (DensePoly.C (d - c) : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  unfold primeFieldLinearFactor FpPoly.X FpPoly.C
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_C, DensePoly.coeff_C,
      DensePoly.coeff_C]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  cases n with
  | zero => simp; grind
  | succ n =>
      cases n with
      | zero => simp; grind
      | succ n => simp; grind

/-- `DensePoly.C` of a nonzero residue divides `1` (it is a unit polynomial). -/
private theorem C_ne_zero_dvd_one {a : ZMod64 p} (ha : a ≠ 0) :
    (DensePoly.C a : FpPoly p) ∣ (1 : FpPoly p) := by
  refine ⟨DensePoly.C (ZMod64.inv a), ?_⟩
  show (1 : FpPoly p) = (DensePoly.C a : FpPoly p) * DensePoly.C (ZMod64.inv a)
  have hmul : (DensePoly.C a : FpPoly p) * DensePoly.C (ZMod64.inv a)
      = DensePoly.C (a * ZMod64.inv a) := by
    rw [FpPoly.C_mul_eq_scale]
    rw [show (DensePoly.C (ZMod64.inv a) : FpPoly p)
          = DensePoly.scale (ZMod64.inv a) (1 : FpPoly p) from
        (FpPoly.scale_one_poly (ZMod64.inv a)).symm]
    rw [FpPoly.scale_scale, FpPoly.scale_one_poly]
  rw [hmul, ZMod64.mul_inv_eq_one_of_ne_zero ha]
  rfl

omit [ZMod64.PrimeModulus p] in
private theorem dvd_trans_local {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, FpPoly.mul_assoc]

/-- Distinct prime-field linear factors are coprime: any common divisor is a unit. -/
theorem primeFieldLinearFactor_distinct_common_dvd_one {c d : ZMod64 p}
    (hcd : c ≠ d) (e : FpPoly p)
    (hec : e ∣ primeFieldLinearFactor c)
    (hed : e ∣ primeFieldLinearFactor d) :
    e ∣ (1 : FpPoly p) := by
  have hdiff : e ∣ (primeFieldLinearFactor c - primeFieldLinearFactor d) :=
    DensePoly.dvd_sub_poly hec hed
  rw [primeFieldLinearFactor_sub_eq c d] at hdiff
  have hdc_ne : (d - c) ≠ (0 : ZMod64 p) := by
    intro hzero
    apply hcd
    have : c = d := by grind
    exact this
  exact dvd_trans_local hdiff (C_ne_zero_dvd_one hdc_ne)

/-- If `a` is coprime with both `b` and `c`, it is coprime with `b * c`. -/
private theorem coprime_mul_of_coprime_both (a b c : FpPoly p)
    (h_ab : ∀ e : FpPoly p, e ∣ a → e ∣ b → e ∣ (1 : FpPoly p))
    (h_ac : ∀ e : FpPoly p, e ∣ a → e ∣ c → e ∣ (1 : FpPoly p)) :
    ∀ e : FpPoly p, e ∣ a → e ∣ b * c → e ∣ (1 : FpPoly p) := by
  intro e he_a he_bc
  have he_coprime_b : ∀ d : FpPoly p, d ∣ b → d ∣ e → d ∣ (1 : FpPoly p) :=
    fun d hdb hde => h_ab d (dvd_trans_local hde he_a) hdb
  have he_c : e ∣ c :=
    FpPoly.dvd_of_dvd_mul_of_common_dvd_one he_bc he_coprime_b
  exact h_ac e he_a he_c

/-- Foldl-shape divisibility: if every linear factor in `xs` divides `f`,
the cumulative `(acc * ∏ (X - C cᵢ))` divides `f` as long as `acc` is coprime
with each new linear factor. -/
private theorem foldl_primeFieldLinearProduct_dvd
    (f : FpPoly p) (xs : List (ZMod64 p)) :
    ∀ (acc : FpPoly p),
      xs.Nodup →
      acc ∣ f →
      (∀ c ∈ xs, primeFieldLinearFactor c ∣ f) →
      (∀ c ∈ xs, ∀ e : FpPoly p,
        e ∣ acc → e ∣ primeFieldLinearFactor c → e ∣ (1 : FpPoly p)) →
      xs.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) acc ∣ f := by
  induction xs with
  | nil =>
      intro acc _ h_acc _ _
      simpa using h_acc
  | cons c rest ih =>
      intro acc h_nodup h_acc h_factors h_coprime
      simp only [List.foldl_cons]
      have h_nodup_rest : rest.Nodup := (List.nodup_cons.mp h_nodup).2
      have h_c_not_rest : c ∉ rest := (List.nodup_cons.mp h_nodup).1
      have h_acc_new : acc * primeFieldLinearFactor c ∣ f :=
        mul_dvd_of_dvd_dvd_common h_acc
          (h_factors c ((List.mem_cons.mpr (Or.inl rfl))))
          (h_coprime c ((List.mem_cons.mpr (Or.inl rfl))))
      have h_coprime_new :
          ∀ d ∈ rest, ∀ e : FpPoly p,
            e ∣ (acc * primeFieldLinearFactor c) →
            e ∣ primeFieldLinearFactor d → e ∣ (1 : FpPoly p) := by
        intro d hd_mem e he_prod he_d
        have hcd : c ≠ d := fun hcd_eq => h_c_not_rest (hcd_eq ▸ hd_mem)
        have h1 : ∀ e' : FpPoly p,
            e' ∣ primeFieldLinearFactor d → e' ∣ acc → e' ∣ (1 : FpPoly p) :=
          fun e' he'_d he'_acc =>
            h_coprime d (List.mem_cons_of_mem c hd_mem) e' he'_acc he'_d
        have h2 : ∀ e' : FpPoly p,
            e' ∣ primeFieldLinearFactor d →
            e' ∣ primeFieldLinearFactor c → e' ∣ (1 : FpPoly p) :=
          fun e' he'_d he'_c =>
            primeFieldLinearFactor_distinct_common_dvd_one (Ne.symm hcd) e'
              he'_d he'_c
        exact coprime_mul_of_coprime_both
          (primeFieldLinearFactor d) acc (primeFieldLinearFactor c) h1 h2
          e he_d he_prod
      have h_factors_rest :
          ∀ d ∈ rest, primeFieldLinearFactor d ∣ f :=
        fun d hd => h_factors d (List.mem_cons_of_mem c hd)
      exact ih (acc * primeFieldLinearFactor c) h_nodup_rest h_acc_new
        h_factors_rest h_coprime_new

/-- The canonical prime-field product divides `xPowSubX 1`. -/
theorem primeFieldLinearProduct_dvd_xPowSubX_one :
    primeFieldLinearProduct (p := p) ∣ xPowSubX (p := p) 1 := by
  unfold primeFieldLinearProduct
  apply foldl_primeFieldLinearProduct_dvd
  · exact ZMod64.values_nodup
  · exact ⟨xPowSubX (p := p) 1, by rw [FpPoly.one_mul]⟩
  · intro c _
    exact primeFieldLinearFactor_dvd_xPowSubX_one c
  · intro c _ e he_acc _
    -- acc = 1, so e ∣ 1 follows from e ∣ acc
    exact he_acc

omit [ZMod64.PrimeModulus p] in
/-- The high coefficients of a prime-field linear factor vanish. -/
private theorem primeFieldLinearFactor_coeff_high (c : ZMod64 p) {n : Nat}
    (hn : 2 ≤ n) : (primeFieldLinearFactor c).coeff n = 0 := by
  unfold primeFieldLinearFactor FpPoly.X FpPoly.C
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_C]
  have hn1 : ¬ n = 1 := by omega
  have hn0 : ¬ n = 0 := by omega
  simp [hn1, hn0]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  grind

/-- Each prime-field linear factor has size 2 (it is genuinely degree 1). -/
theorem primeFieldLinearFactor_size (c : ZMod64 p) :
    (primeFieldLinearFactor c).size = 2 := by
  have h_coeff_1_ne : (primeFieldLinearFactor c).coeff 1 ≠ 0 := by
    rw [primeFieldLinearFactor_coeff_one c]
    exact zmod64_one_ne_zero_of_prime
  have h_lower : 2 ≤ (primeFieldLinearFactor c).size := by
    apply Classical.byContradiction
    intro h
    have hle : (primeFieldLinearFactor c).size ≤ 1 := by omega
    exact h_coeff_1_ne
      (DensePoly.coeff_eq_zero_of_size_le _ hle)
  have h_upper : (primeFieldLinearFactor c).size ≤ 2 := by
    apply Classical.byContradiction
    intro h
    have hgt : 2 < (primeFieldLinearFactor c).size := by omega
    have h_pos : 0 < (primeFieldLinearFactor c).size := by omega
    have h_top_ne :
        (primeFieldLinearFactor c).coeff
          ((primeFieldLinearFactor c).size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size _ h_pos
    apply h_top_ne
    exact primeFieldLinearFactor_coeff_high c (by omega)
  omega

/-- Each prime-field linear factor is monic. -/
theorem primeFieldLinearFactor_monic (c : ZMod64 p) :
    DensePoly.Monic (primeFieldLinearFactor c) := by
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _
    (by rw [primeFieldLinearFactor_size]; omega)]
  rw [primeFieldLinearFactor_size]
  exact primeFieldLinearFactor_coeff_one c

/-- Leading coefficient of a product equals the product of leading coefficients
(no-zero-divisors form). -/
private theorem leadingCoeff_mul_fpoly (a b : FpPoly p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    DensePoly.leadingCoeff (a * b)
      = DensePoly.leadingCoeff a * DensePoly.leadingCoeff b := by
  have ha_pos : 0 < a.size := FpPoly.size_pos_of_ne_zero ha
  have hb_pos : 0 < b.size := FpPoly.size_pos_of_ne_zero hb
  have hab_ne : a * b ≠ 0 := FpPoly.mul_ne_zero_of_ne_zero ha hb
  have hab_pos : 0 < (a * b).size := FpPoly.size_pos_of_ne_zero hab_ne
  have hsize := FpPoly.size_mul_eq_add_sub_one a b ha hb
  have hindex : (a * b).size - 1 = a.size - 1 + (b.size - 1) := by omega
  rw [DensePoly.leadingCoeff_eq_coeff_last (a * b) hab_pos]
  rw [hindex]
  rw [DensePoly.leadingCoeff_eq_coeff_last a ha_pos]
  rw [DensePoly.leadingCoeff_eq_coeff_last b hb_pos]
  exact ZMod64.coeff_mul_at_top a b ha_pos hb_pos

/-- Multiplying two monic prime-field polynomials yields a monic polynomial. -/
private theorem monic_mul_monic (a b : FpPoly p)
    (ha_ne : a ≠ 0) (hb_ne : b ≠ 0)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b) :
    DensePoly.Monic (a * b) := by
  unfold DensePoly.Monic
  rw [leadingCoeff_mul_fpoly a b ha_ne hb_ne]
  unfold DensePoly.Monic at ha hb
  rw [ha, hb]
  grind

/-- Foldl induction: size grows by one for each linear factor multiplied in. -/
private theorem foldl_size_and_monic
    (xs : List (ZMod64 p)) :
    ∀ (acc : FpPoly p),
      acc ≠ 0 →
      DensePoly.Monic acc →
      (xs.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) acc) ≠ 0 ∧
      DensePoly.Monic (xs.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) acc) ∧
      (xs.foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) acc).size
        = acc.size + xs.length := by
  induction xs with
  | nil =>
      intro acc h_ne h_monic
      refine ⟨h_ne, h_monic, ?_⟩
      simp
  | cons c rest ih =>
      intro acc h_ne h_monic
      simp only [List.foldl_cons]
      have h_factor_ne : primeFieldLinearFactor c ≠ 0 :=
        primeFieldLinearFactor_ne_zero c
      have h_factor_monic : DensePoly.Monic (primeFieldLinearFactor c) :=
        primeFieldLinearFactor_monic c
      have h_factor_size : (primeFieldLinearFactor c).size = 2 :=
        primeFieldLinearFactor_size c
      have h_new_ne : acc * primeFieldLinearFactor c ≠ 0 :=
        FpPoly.mul_ne_zero_of_ne_zero h_ne h_factor_ne
      have h_new_monic : DensePoly.Monic (acc * primeFieldLinearFactor c) :=
        monic_mul_monic acc (primeFieldLinearFactor c) h_ne h_factor_ne
          h_monic h_factor_monic
      have h_acc_pos : 0 < acc.size := FpPoly.size_pos_of_ne_zero h_ne
      have h_new_size : (acc * primeFieldLinearFactor c).size = acc.size + 1 := by
        rw [FpPoly.size_mul_eq_add_sub_one acc _ h_ne h_factor_ne, h_factor_size]
        omega
      have h_ih := ih (acc * (FpPoly.X - FpPoly.C c)) h_new_ne h_new_monic
      refine ⟨h_ih.1, h_ih.2.1, ?_⟩
      have h_new_size' : (acc * (FpPoly.X - FpPoly.C c)).size = acc.size + 1 :=
        h_new_size
      rw [h_ih.2.2, h_new_size']
      simp [List.length_cons]
      omega

/-- The constant polynomial `1` over a prime modulus is nonzero. -/
private theorem fpPoly_one_ne_zero : (1 : FpPoly p) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
  change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_zero] at hcoeff
  have hone_coeff : (1 : FpPoly p).coeff 0 = (1 : ZMod64 p) := by
    change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (1 : ZMod64 p)
    rw [DensePoly.coeff_C]
    simp
  rw [hone_coeff] at hcoeff
  exact zmod64_one_ne_zero_of_prime hcoeff

/-- The constant polynomial `1` over a prime modulus has size `1`. -/
private theorem fpPoly_one_size : (1 : FpPoly p).size = 1 := by
  have h_le : (1 : FpPoly p).size ≤ 1 := by
    change (DensePoly.C (1 : ZMod64 p) : FpPoly p).size ≤ 1
    exact DensePoly.size_C_le_one (1 : ZMod64 p)
  have h_ge : 1 ≤ (1 : FpPoly p).size := FpPoly.size_pos_of_ne_zero fpPoly_one_ne_zero
  omega

/-- The constant polynomial `1` over a prime modulus is monic. -/
private theorem fpPoly_one_monic : DensePoly.Monic (1 : FpPoly p) := by
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _ (by rw [fpPoly_one_size]; omega)]
  rw [fpPoly_one_size]
  change (DensePoly.C (1 : ZMod64 p)).coeff 0 = 1
  rw [DensePoly.coeff_C]
  simp

/-- The canonical prime-field product has size `p + 1`. -/
theorem primeFieldLinearProduct_size :
    (primeFieldLinearProduct (p := p)).size = p + 1 := by
  unfold primeFieldLinearProduct
  have h := foldl_size_and_monic (p := p) (ZMod64.values p) 1
    fpPoly_one_ne_zero fpPoly_one_monic
  rw [h.2.2, fpPoly_one_size, ZMod64.values_length]
  omega

/-- The canonical prime-field product is nonzero. -/
theorem primeFieldLinearProduct_ne_zero :
    primeFieldLinearProduct (p := p) ≠ 0 := by
  unfold primeFieldLinearProduct
  exact (foldl_size_and_monic (p := p) (ZMod64.values p) 1
    fpPoly_one_ne_zero fpPoly_one_monic).1

/-- The canonical prime-field product is monic. -/
theorem primeFieldLinearProduct_monic :
    DensePoly.Monic (primeFieldLinearProduct (p := p)) := by
  unfold primeFieldLinearProduct
  exact (foldl_size_and_monic (p := p) (ZMod64.values p) 1
    fpPoly_one_ne_zero fpPoly_one_monic).2.1

/-! ### `xPowSubX 1` shape and the final identity -/

/-- The coefficient of `xPowSubX 1` at index `p` is `1` (the leading position). -/
private theorem xPowSubX_one_coeff_p :
    (xPowSubX (p := p) 1).coeff p = (1 : ZMod64 p) := by
  unfold xPowSubX FpPoly.X
  rw [Nat.pow_one]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_monomial]
  have hp_pos : 2 ≤ p :=
    Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
  have hp1 : ¬ p = 1 := by omega
  simp [hp1]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  grind

/-- High coefficients of `xPowSubX 1` vanish (`n > p`). -/
private theorem xPowSubX_one_coeff_high {n : Nat} (hn : p < n) :
    (xPowSubX (p := p) 1).coeff n = 0 := by
  unfold xPowSubX FpPoly.X
  rw [Nat.pow_one]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_monomial]
  have hp_pos : 2 ≤ p :=
    Hex.Nat.Prime.two_le (ZMod64.PrimeModulus.prime (p := p))
  have hn_ne_p : ¬ n = p := by omega
  have hn_ne_1 : ¬ n = 1 := by omega
  simp [hn_ne_p, hn_ne_1]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  grind

/-- `xPowSubX 1` has size `p + 1`. -/
theorem xPowSubX_one_size : (xPowSubX (p := p) 1).size = p + 1 := by
  have h_coeff_p_ne : (xPowSubX (p := p) 1).coeff p ≠ 0 := by
    rw [xPowSubX_one_coeff_p]
    exact zmod64_one_ne_zero_of_prime
  have h_lower : p + 1 ≤ (xPowSubX (p := p) 1).size := by
    apply Classical.byContradiction
    intro h
    have hle : (xPowSubX (p := p) 1).size ≤ p := by omega
    exact h_coeff_p_ne (DensePoly.coeff_eq_zero_of_size_le _ hle)
  have h_upper : (xPowSubX (p := p) 1).size ≤ p + 1 := by
    apply Classical.byContradiction
    intro h
    have hgt : p + 1 < (xPowSubX (p := p) 1).size := by omega
    have h_pos : 0 < (xPowSubX (p := p) 1).size := by omega
    have h_top_ne :
        (xPowSubX (p := p) 1).coeff ((xPowSubX (p := p) 1).size - 1) ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size _ h_pos
    apply h_top_ne
    apply xPowSubX_one_coeff_high
    omega
  omega

/-- `xPowSubX 1` is monic. -/
theorem xPowSubX_one_monic :
    DensePoly.Monic (xPowSubX (p := p) 1) := by
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _
    (by rw [xPowSubX_one_size]; omega)]
  rw [xPowSubX_one_size]
  change (xPowSubX (p := p) 1).coeff (p + 1 - 1) = 1
  have : p + 1 - 1 = p := by omega
  rw [this]
  exact xPowSubX_one_coeff_p

/-- A monic polynomial dividing another monic polynomial of equal size equals it. -/
private theorem eq_of_dvd_of_size_eq_of_monic
    {a b : FpPoly p} (ha_ne : a ≠ 0) (hb_ne : b ≠ 0)
    (hdvd : a ∣ b) (hsize : a.size = b.size)
    (ha_monic : DensePoly.Monic a) (hb_monic : DensePoly.Monic b) :
    a = b := by
  rcases hdvd with ⟨q, hq⟩
  have hq_ne : q ≠ 0 := by
    intro hq_zero
    apply hb_ne
    rw [hq, hq_zero, FpPoly.mul_zero]
  have ha_pos : 0 < a.size := FpPoly.size_pos_of_ne_zero ha_ne
  have hq_pos : 0 < q.size := FpPoly.size_pos_of_ne_zero hq_ne
  have hb_eq_size : b.size = a.size + q.size - 1 := by
    rw [hq]
    exact FpPoly.size_mul_eq_add_sub_one a q ha_ne hq_ne
  have hq_size_one : q.size = 1 := by
    rw [hb_eq_size] at hsize
    omega
  -- q has size 1, so q = DensePoly.C (q.coeff 0).
  have hq_eq_C : q = (DensePoly.C (q.coeff 0) : FpPoly p) := by
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_C]
    cases n with
    | zero => simp
    | succ n =>
        simp
        apply DensePoly.coeff_eq_zero_of_size_le
        omega
  -- Leading coeff: 1 = leadingCoeff b = leadingCoeff a * leadingCoeff q = 1 * (q.coeff 0)
  have hlead_eq : DensePoly.leadingCoeff b
      = DensePoly.leadingCoeff a * DensePoly.leadingCoeff q := by
    rw [hq]
    exact leadingCoeff_mul_fpoly a q ha_ne hq_ne
  have hq_lead : DensePoly.leadingCoeff q = q.coeff 0 := by
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hq_pos, hq_size_one]
  have hq_coeff0 : q.coeff 0 = 1 := by
    unfold DensePoly.Monic at ha_monic hb_monic
    rw [ha_monic, hq_lead, hb_monic] at hlead_eq
    have : (1 : ZMod64 p) = 1 * q.coeff 0 := hlead_eq
    grind
  rw [hq, hq_eq_C, hq_coeff0]
  show a = a * (DensePoly.C (1 : ZMod64 p))
  rw [show (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 from rfl]
  rw [FpPoly.mul_one]

/-- The variable prime-field product identity: the canonical product over field
constants equals `xPowSubX 1`. This is the headline deliverable for #4085. -/
theorem primeFieldProduct_X_eq_xPowSubX :
    (ZMod64.values p).foldl
      (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1 =
        xPowSubX (p := p) 1 := by
  change primeFieldLinearProduct (p := p) = xPowSubX (p := p) 1
  apply eq_of_dvd_of_size_eq_of_monic
    primeFieldLinearProduct_ne_zero
    (by
      intro h
      have h_coeff_p_ne : (xPowSubX (p := p) 1).coeff p ≠ 0 := by
        rw [xPowSubX_one_coeff_p]
        exact zmod64_one_ne_zero_of_prime
      apply h_coeff_p_ne
      rw [h]
      exact DensePoly.coeff_zero p)
    primeFieldLinearProduct_dvd_xPowSubX_one
    (by rw [primeFieldLinearProduct_size, xPowSubX_one_size])
    primeFieldLinearProduct_monic
    xPowSubX_one_monic

/-- Substituting `w` into `xPowSubX 1 = X^p - X` yields `linearPow w p - w`.
This is deliverable 3 of issue #4187 and the missing transport step that
takes the variable identity `primeFieldProduct_X_eq_xPowSubX` to its
witness-substituted form. -/
theorem compose_xPowSubX_one (w : FpPoly p) :
    DensePoly.compose (xPowSubX (p := p) 1) w =
      FpPoly.linearPow w p - w := by
  have hxPow : xPowSubX (p := p) 1 = FpPoly.linearPow FpPoly.X p - FpPoly.X := by
    unfold xPowSubX
    show DensePoly.monomial (p ^ 1) (1 : ZMod64 p) - FpPoly.X =
      FpPoly.linearPow FpPoly.X p - FpPoly.X
    congr 1
    rw [show (FpPoly.X : FpPoly p) = DensePoly.monomial 1 (1 : ZMod64 p) from rfl]
    rw [FpPoly.linearPow_monomial_one]
    congr 1
    exact Nat.pow_one p
  rw [hxPow]
  exact FpPoly.compose_linearPow_X_sub_X w p

/-- Substituting an arbitrary witness into the prime-field product identity. -/
theorem primeFieldProduct_witness_eq (w : FpPoly p) :
    (ZMod64.values p).foldl
      (fun acc c => acc * (w - FpPoly.C c)) 1 =
        FpPoly.linearPow w p - w := by
  rw [← FpPoly.compose_primeFieldLinearProduct w]
  rw [primeFieldProduct_X_eq_xPowSubX]
  exact compose_xPowSubX_one w

/-- Divisibility by `w^p - w` transports to the canonical witness product. -/
theorem dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self
    {f w : FpPoly p}
    (hdvd : f ∣ FpPoly.linearPow w p - w) :
    f ∣ (ZMod64.values p).foldl
      (fun acc c => acc * (w - FpPoly.C c)) 1 := by
  rw [primeFieldProduct_witness_eq w]
  exact hdvd

/-! ### Structural lemmas

These small consequences only use the foundational lemmas above plus
existing infrastructure in `HexBerlekamp.Irreducibility`. -/

omit [ZMod64.PrimeModulus p] in
/-- Local divisibility transitivity for `FpPoly p`. -/
private theorem fp_dvd_trans {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, FpPoly.mul_assoc]

omit [ZMod64.PrimeModulus p] in
/-- A polynomial of positive degree is not the unit polynomial. -/
theorem isUnitPolynomial_eq_false_of_pos_degree
    {g : FpPoly p} (hpos : 0 < g.degree?.getD 0) :
    isUnitPolynomial g = false := by
  unfold isUnitPolynomial
  cases hdeg : g.degree? with
  | none => rfl
  | some k =>
    have hk : k = g.degree?.getD 0 := by simp [hdeg]
    subst hk
    cases hcase : g.degree?.getD 0 with
    | zero =>
        simp [hcase] at hpos
    | succ _ => rfl

/--
If `gcd(f, q)` is a unit polynomial and `g` divides both `f` and `q`,
then `g` is itself a unit polynomial.
-/
theorem isUnitPolynomial_of_dvd_gcd_isUnit
    {f q g : FpPoly p}
    (hgf : g ∣ f) (hgq : g ∣ q)
    (hgcd : isUnitPolynomial (DensePoly.gcd f q) = true) :
    isUnitPolynomial g = true :=
  isUnitPolynomial_of_dvd_isUnitPolynomial
    (DensePoly.dvd_gcd g f q hgf hgq) hgcd

/-! ### Soundness theorem -/

/--
Soundness of the executable Rabin test against the project-side
`FpPoly.Irreducible` predicate.

The proof orchestrates the foundational lemmas above. The combinatorial
shape (decomposing `rabinTest`, picking a monic irreducible factor of
size strictly between `0` and `n`, routing through a maximal proper
divisor, and contradicting the gcd leg) lives here. The heavy
mathematical content (Rabin's degree theorem in both directions,
finite-field factor existence, the absolute–modular Frobenius identity,
and the `xPowSubX` divisibility chain) is delegated to the foundational
sorries above.
-/
theorem rabinTest_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hrabin : rabinTest f hmonic = true) :
    FpPoly.Irreducible f := by
  -- Decompose the executable test surface.
  simp only [rabinTest, Bool.and_eq_true, decide_eq_true_eq] at hrabin
  obtain ⟨⟨hpos, hdivides⟩, hwitnesses⟩ := hrabin
  -- Modular and absolute forms of the divisibility leg.
  have hdiff_isZero :
      (frobeniusDiffMod f hmonic (basisSize f)).isZero = true := by
    unfold rabinDividesTest at hdivides
    exact hdivides
  have hf_dvd_xPowSubX_n :
      f ∣ xPowSubX (p := p) (basisSize f) :=
    (dvd_xPowSubX_iff_frobeniusDiffMod_isZero f hmonic (basisSize f)).mpr
      hdiff_isZero
  -- `f ≠ 0` from positive degree.
  have hf_ne_zero : f ≠ 0 := ne_zero_of_pos_degree hpos
  refine ⟨hf_ne_zero, ?_⟩
  intro a b hab
  -- Reduce the disjunction to a contradiction proof using classical case analysis.
  by_cases ha_unit : a.degree? = some 0
  · exact Or.inl ha_unit
  refine Or.inr ?_
  by_cases hb_unit : b.degree? = some 0
  · exact hb_unit
  exfalso
  -- Both factors are nonconstant. Derive a contradiction with `rabinTest`.
  have ha_ne_zero : a ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb_ne_zero : b ≠ 0 := by
    have hba : b * a = f := by rw [FpPoly.mul_comm]; exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha_pos : 0 < a.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit ha_ne_zero ha_unit
  have hb_pos : 0 < b.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit hb_ne_zero hb_unit
  have ha_lt : a.degree?.getD 0 < basisSize f :=
    factor_degree_lt_basisSize hab ha_ne_zero hb_pos
  -- Pick a monic irreducible factor `g` of `a`.
  obtain ⟨g, hg_irr, hg_monic, hg_dvd_a, hg_deg_pos, hg_deg_le_a⟩ :=
    exists_monic_irreducible_factor_of_factor hmonic hab ha_pos
  -- `g ∣ f` via `g ∣ a ∣ f`.
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a with ⟨r, hr⟩
    refine ⟨r * b, ?_⟩
    calc f = a * b := hab.symm
      _ = (g * r) * b := by rw [hr]
      _ = g * (r * b) := by rw [FpPoly.mul_assoc]
  -- `g ∣ X^(p^n) - X` from transitivity.
  have hg_dvd_xPowSubX_n : g ∣ xPowSubX (p := p) (basisSize f) :=
    fp_dvd_trans hg_dvd_f hf_dvd_xPowSubX_n
  -- Rabin: `deg g ∣ basisSize f`.
  have hdeg_dvd : g.degree?.getD 0 ∣ basisSize f :=
    degree_dvd_of_irreducible_dvd_xPowSubX hg_irr hg_monic hg_deg_pos
      hg_dvd_xPowSubX_n
  -- `deg g < basisSize f` because `deg g ≤ deg a < basisSize f`.
  have hdeg_lt : g.degree?.getD 0 < basisSize f :=
    Nat.lt_of_le_of_lt hg_deg_le_a ha_lt
  -- Route `deg g` through some maximal proper divisor `m` of `basisSize f`.
  obtain ⟨m, hm_mem, hdeg_dvd_m⟩ :=
    exists_maximalProperDivisor_dvd hg_deg_pos hdeg_dvd hdeg_lt
  -- `g ∣ X^(p^(deg g)) - X` (Rabin backward direction).
  have hg_dvd_xPowSubX_deg : g ∣ xPowSubX (p := p) (g.degree?.getD 0) :=
    irreducible_dvd_xPowSubX_degree hg_irr hg_monic hg_deg_pos
  -- `X^(p^(deg g)) - X ∣ X^(p^m) - X` via the divisibility chain.
  have hxPow_dvd_xPow : xPowSubX (p := p) (g.degree?.getD 0) ∣
      xPowSubX (p := p) m :=
    xPowSubX_dvd_of_dvd hdeg_dvd_m
  have hg_dvd_xPowSubX_m : g ∣ xPowSubX (p := p) m :=
    fp_dvd_trans hg_dvd_xPowSubX_deg hxPow_dvd_xPow
  -- Lift to `g ∣ frobeniusDiffMod f hmonic m`.
  have hg_dvd_frob : g ∣ frobeniusDiffMod f hmonic m :=
    dvd_frobeniusDiffMod_of_dvd_dvd hmonic hg_dvd_f hg_dvd_xPowSubX_m
  -- The gcd leg of `rabinTest` at `m` says the gcd is a unit polynomial.
  have hcoprime : rabinCoprimeTest f hmonic m = true :=
    rabinCoprimeTest_of_mem_maximalProperDivisors f hmonic hwitnesses hm_mem
  have hgcd_unit :
      isUnitPolynomial (DensePoly.gcd f (frobeniusDiffMod f hmonic m)) = true := by
    unfold rabinCoprimeTest frobeniusDiffMod at hcoprime
    -- `rabinCoprimeTest` is exactly `isUnitPolynomial (gcd f (frobeniusDiffMod _ _ m))`.
    exact hcoprime
  -- A common divisor of `f` and `frobeniusDiffMod f hmonic m` is a unit.
  have hg_unit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_dvd_gcd_isUnit hg_dvd_f hg_dvd_frob hgcd_unit
  -- But `g` has positive degree, contradiction.
  have hg_not_unit : isUnitPolynomial g = false :=
    isUnitPolynomial_eq_false_of_pos_degree hg_deg_pos
  rw [hg_not_unit] at hg_unit
  exact Bool.noConfusion hg_unit

/-! ### Convenience corollary for the certificate checker -/

/--
Accepted executable irreducibility certificates imply project-side
`FpPoly.Irreducible`, composing
`checkIrreducibilityCertificate_rabinTest` with the Rabin soundness
theorem above.
-/
theorem checkIrreducibilityCertificate_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificate f hmonic cert = true) :
    FpPoly.Irreducible f :=
  rabinTest_imp_irreducible f hmonic
    (checkIrreducibilityCertificate_rabinTest f hmonic cert hcheck)

/--
The kernel-reducible certificate checker also implies project-side
`FpPoly.Irreducible`, composing the linear checker soundness theorem with
Rabin soundness.
-/
theorem checkIrreducibilityCertificateLinear_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificateLinear f hmonic cert = true) :
    FpPoly.Irreducible f :=
  rabinTest_imp_irreducible f hmonic
    (checkIrreducibilityCertificateLinear_rabinTest f hmonic cert hcheck)

/--
The incremental kernel-reducible certificate checker also implies
project-side `FpPoly.Irreducible`.
-/
theorem checkIrreducibilityCertificateLinearIncremental_imp_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificateLinearIncremental f hmonic cert = true) :
    FpPoly.Irreducible f :=
  rabinTest_imp_irreducible f hmonic
    (checkIrreducibilityCertificateLinearIncremental_rabinTest f hmonic cert hcheck)

/-! ### Distinct-degree saturation infrastructure

These lemmas package the Leibniz-rule consequence used by the distinct-degree
factorization assembly: if `r` is square-free (i.e. `gcd r r' = 1`) and
`c = gcd r d`, then `r/c` is coprime to `d`. The proof goes through the
"strong square-free" characterization that any squared divisor of `r` is a
unit. -/

theorem isUnitPolynomial_one_FpPoly : isUnitPolynomial (1 : FpPoly p) = true := by
  unfold isUnitPolynomial
  change (match DensePoly.degree? (DensePoly.C (1 : ZMod64 p)) with
    | some 0 => true
    | _ => false) = true
  have hone_ne_zero : (1 : ZMod64 p) ≠ 0 := by
    intro h
    have : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat := congrArg ZMod64.toNat h
    rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
        show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
        Nat.mod_eq_of_lt (by
          have h2 : 2 ≤ p := (ZMod64.PrimeModulus.prime (p := p)).two_le
          omega : 1 < p)] at this
    exact absurd this (by omega)
  have hcoeffs : (DensePoly.C (1 : ZMod64 p)).coeffs = #[(1 : ZMod64 p)] :=
    DensePoly.coeffs_C_of_ne_zero hone_ne_zero
  simp [DensePoly.degree?, DensePoly.size, hcoeffs]

theorem dvd_one_of_isUnitPolynomial
    {u : FpPoly p} (hu : isUnitPolynomial u = true) :
    u ∣ (1 : FpPoly p) := by
  have hu_deg : u.degree? = some 0 := by
    unfold isUnitPolynomial at hu
    cases hdeg : u.degree? with
    | none =>
        rw [hdeg] at hu
        simp at hu
    | some k =>
        rw [hdeg] at hu
        cases k with
        | zero => rfl
        | succ _ => simp at hu
  have hu_size_ne_zero : u.size ≠ 0 := by
    intro hsize
    unfold DensePoly.degree? at hu_deg
    simp [hsize] at hu_deg
  have hu_size : u.size = 1 := by
    unfold DensePoly.degree? at hu_deg
    simp [hu_size_ne_zero] at hu_deg
    omega
  have hmod : (1 : FpPoly p) % u = 0 := by
    show (DensePoly.divMod (1 : FpPoly p) u).2 = 0
    apply DensePoly.divMod_remainder_eq_zero_of_degree_zero_core
    · exact hu_size
    · intro a
      have hpos : 0 < u.size := by omega
      have hidx : u.coeffs.size - 1 < u.coeffs.size := by
        simpa [DensePoly.size] using Nat.sub_one_lt_of_lt hpos
      have hlead_eq : u.leadingCoeff = u.coeff (u.size - 1) := by
        unfold DensePoly.leadingCoeff DensePoly.coeff
        change u.coeffs.back?.getD (0 : ZMod64 p) =
          u.coeffs.getD (u.coeffs.size - 1) (Zero.zero : ZMod64 p)
        rw [Array.back?_eq_getElem?, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_getElem hidx]
        rfl
      have hlead_ne : u.leadingCoeff ≠ (Zero.zero : ZMod64 p) := by
        rw [hlead_eq]
        exact DensePoly.coeff_last_ne_zero_of_pos_size u hpos
      have hinv : ZMod64.inv u.leadingCoeff * u.leadingCoeff = (1 : ZMod64 p) :=
        ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) hlead_ne
      have hmul : (a / u.leadingCoeff) * u.leadingCoeff = a := by
        change (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff = a
        calc
          (ZMod64.mul a (ZMod64.inv u.leadingCoeff)) * u.leadingCoeff
              = a * (ZMod64.inv u.leadingCoeff * u.leadingCoeff) := by
                  exact Lean.Grind.Semiring.mul_assoc a (ZMod64.inv u.leadingCoeff)
                    u.leadingCoeff
          _ = a * (1 : ZMod64 p) := by rw [hinv]
          _ = a := Lean.Grind.Semiring.mul_one a
      change a - (a / u.leadingCoeff) * u.leadingCoeff = (Zero.zero : ZMod64 p)
      rw [hmul]
      change ZMod64.sub a a = (Zero.zero : ZMod64 p)
      apply ZMod64.ext
      apply UInt64.toNat_inj.mp
      change (ZMod64.sub a a).toNat = (Zero.zero : ZMod64 p).toNat
      rw [ZMod64.toNat_sub]
      have hsum : a.toNat + (p - a.toNat) = p := by
        have ha : a.toNat < p := a.toNat_lt
        omega
      rw [hsum, Nat.mod_self]
      exact ZMod64.toNat_zero.symm
  refine ⟨(1 : FpPoly p) / u, ?_⟩
  have hspec := DensePoly.div_mul_add_mod (1 : FpPoly p) u
  rw [hmod] at hspec
  exact ((DensePoly.mul_comm_poly u ((1 : FpPoly p) / u)).trans
    ((DensePoly.add_zero_poly (((1 : FpPoly p) / u) * u)).symm.trans hspec)).symm

omit [ZMod64.PrimeModulus p] in
private theorem dvd_derivative_self_mul_self (g : FpPoly p) :
    g ∣ DensePoly.derivative (g * g) := by
  refine ⟨DensePoly.derivative g + DensePoly.derivative g, ?_⟩
  -- Use calc-style with `:=` proofs (which check up to defeq) to avoid
  -- rw's syntactic-match limitations across instance diamond.
  calc DensePoly.derivative (g * g)
      = DensePoly.derivative g * g + g * DensePoly.derivative g :=
        DensePoly.derivative_mul g g
    _ = g * DensePoly.derivative g + g * DensePoly.derivative g :=
        congrArg (· + g * DensePoly.derivative g)
          (DensePoly.mul_comm_poly (DensePoly.derivative g) g)
    _ = g * (DensePoly.derivative g + DensePoly.derivative g) :=
        (DensePoly.mul_add_right_poly g
          (DensePoly.derivative g) (DensePoly.derivative g)).symm

omit [ZMod64.PrimeModulus p] in
private theorem dvd_derivative_of_squared_dvd
    {r g : FpPoly p} (hgg : g * g ∣ r) :
    g ∣ DensePoly.derivative r := by
  rcases hgg with ⟨h, hr⟩
  rcases dvd_derivative_self_mul_self g with ⟨k, hk⟩
  refine ⟨k * h + g * DensePoly.derivative h, ?_⟩
  calc DensePoly.derivative r
      = DensePoly.derivative (g * g * h) := by rw [hr]
    _ = DensePoly.derivative (g * g) * h + (g * g) * DensePoly.derivative h :=
        DensePoly.derivative_mul (g * g) h
    _ = (g * k) * h + (g * g) * DensePoly.derivative h := by rw [hk]
    _ = g * (k * h) + g * (g * DensePoly.derivative h) := by
        congr 1
        · exact DensePoly.mul_assoc_poly g k h
        · exact DensePoly.mul_assoc_poly g g (DensePoly.derivative h)
    _ = g * (k * h + g * DensePoly.derivative h) :=
        (DensePoly.mul_add_right_poly g (k * h) (g * DensePoly.derivative h)).symm

/-- Adapter from the strict executable-gcd form of square-freeness
(`DensePoly.gcd r r' = 1`) to the relaxed common-divisor form
(`∀ d, d ∣ r → d ∣ r' → isUnitPolynomial d`).  The relaxed form is the
shape the soundness chain culminating in `berlekampFactor_singleton_irreducible`
consumes; the strict form is what existing in-tree callers carry, so this
adapter lets them feed the chain unchanged. -/
theorem squareFree_common_of_gcd_eq_one
    {r : FpPoly p}
    (hsf : DensePoly.gcd r (DensePoly.derivative r) = 1) :
    ∀ d, d ∣ r → d ∣ DensePoly.derivative r → isUnitPolynomial d = true := by
  intro d hda hdb
  have hd_dvd_gcd : d ∣ DensePoly.gcd r (DensePoly.derivative r) :=
    DensePoly.dvd_gcd d r (DensePoly.derivative r) hda hdb
  rw [hsf] at hd_dvd_gcd
  exact isUnitPolynomial_of_dvd_isUnitPolynomial hd_dvd_gcd isUnitPolynomial_one_FpPoly

omit [ZMod64.PrimeModulus p] in
theorem isUnitPolynomial_of_squareFree_of_squared_dvd
    {r g : FpPoly p}
    (hsf : ∀ d, d ∣ r → d ∣ DensePoly.derivative r → isUnitPolynomial d = true)
    (hgg : g * g ∣ r) :
    isUnitPolynomial g = true := by
  have hgr : g ∣ r := by
    rcases hgg with ⟨b, hb⟩
    refine ⟨g * b, ?_⟩
    rw [hb]
    exact DensePoly.mul_assoc_poly g g b
  have hgr' : g ∣ DensePoly.derivative r := dvd_derivative_of_squared_dvd hgg
  exact hsf g hgr hgr'

/-- Helper: `c ∣ r → r = c * (r / c)` for FpPoly. -/
private theorem fp_eq_mul_div_of_dvd
    {r c : FpPoly p} (hc_dvd_r : c ∣ r) :
    r = c * (r / c) := by
  have hmod : r % c = 0 := DensePoly.mod_eq_zero_of_dvd r c hc_dvd_r
  have hspec := DensePoly.div_mul_add_mod r c
  rw [hmod] at hspec
  -- `hspec : r / c * c + 0 = r`. Need `r = c * (r / c)`.
  have hcomm : (r / c) * c = c * (r / c) := DensePoly.mul_comm_poly _ _
  -- `r / c * c + 0 = r / c * c`
  have hadd : (r / c) * c + 0 = (r / c) * c := DensePoly.add_zero_poly _
  exact (hspec.symm.trans hadd).trans hcomm

omit [ZMod64.PrimeModulus p] in
/-- Ring rearrangement: `(g * e) * (g * a) = (g * g) * (e * a)`. -/
private theorem fp_swap_inner_mul (g e a : FpPoly p) :
    (g * e) * (g * a) = (g * g) * (e * a) := by
  calc (g * e) * (g * a)
      = g * (e * (g * a)) := DensePoly.mul_assoc_poly g e (g * a)
    _ = g * ((e * g) * a) :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly e g a).symm
    _ = g * ((g * e) * a) :=
        congrArg (fun x => g * (x * a)) (DensePoly.mul_comm_poly e g)
    _ = g * (g * (e * a)) :=
        congrArg (g * ·) (DensePoly.mul_assoc_poly g e a)
    _ = (g * g) * (e * a) := (DensePoly.mul_assoc_poly g g (e * a)).symm

omit [ZMod64.PrimeModulus p] in
/-- Ring rearrangement: `c * (g * a) = g * (c * a)`. -/
private theorem fp_swap_left_mul (c g a : FpPoly p) :
    c * (g * a) = g * (c * a) := by
  calc c * (g * a)
      = (c * g) * a := (DensePoly.mul_assoc_poly c g a).symm
    _ = (g * c) * a :=
        congrArg (· * a) (DensePoly.mul_comm_poly c g)
    _ = g * (c * a) := DensePoly.mul_assoc_poly g c a

theorem common_dvd_one_of_squareFree_mul
    {a b d : FpPoly p}
    (hsquareFree : ∀ e, e ∣ (a * b) → e ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial e = true)
    (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ (1 : FpPoly p) := by
  have hdd_dvd_ab : d * d ∣ a * b := by
    rcases hda with ⟨a', ha'⟩
    rcases hdb with ⟨b', hb'⟩
    refine ⟨a' * b', ?_⟩
    calc a * b
        = (d * a') * (d * b') := by rw [ha', hb']
      _ = (d * d) * (a' * b') := fp_swap_inner_mul d a' b'
  exact dvd_one_of_isUnitPolynomial
    (isUnitPolynomial_of_squareFree_of_squared_dvd hsquareFree hdd_dvd_ab)

/--
Square-free product specialization of
`exists_reduced_crtZeroOne_kernelWitness_of_coprime_split`.  The extra monicity
hypothesis on the executable gcd connects the common-divisor form supplied by
square-freeness to the `gcd a b = 1` surface used by the XGCD-backed CRT
candidate.
-/
theorem exists_reduced_crtZeroOne_kernelWitness_of_squareFree_split
    (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hsquareFree : ∀ d, d ∣ (a * b) → d ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial d = true)
    (hgcd_monic : DensePoly.Monic (DensePoly.gcd a b)) :
    ∃ h : FpPoly p,
      h = crtZeroOneXGCDCandidate a b % (a * b) ∧
      (a * b) ∣ (FpPoly.linearPow h (p ^ 1) - h) ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b) := by
  have hgcd : DensePoly.gcd a b = 1 :=
    FpPoly.gcd_eq_one_of_monic_of_common_dvd_one a b hgcd_monic
      (fun d hda hdb => common_dvd_one_of_squareFree_mul hsquareFree hda hdb)
  exact exists_reduced_crtZeroOne_kernelWitness_of_coprime_split
    a b ha hb ha_pos hb_pos hgcd

theorem isUnitPolynomial_gcd_quotient_of_squareFree
    (r d : FpPoly p)
    (hsf : DensePoly.gcd r (DensePoly.derivative r) = 1) :
    isUnitPolynomial (DensePoly.gcd (r / DensePoly.gcd r d) d) = true := by
  have hc_dvd_r : DensePoly.gcd r d ∣ r := DensePoly.gcd_dvd_left r d
  have hr_eq : r = DensePoly.gcd r d * (r / DensePoly.gcd r d) :=
    fp_eq_mul_div_of_dvd hc_dvd_r
  have hg_dvd_quot :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r / DensePoly.gcd r d :=
    DensePoly.gcd_dvd_left _ _
  have hg_dvd_d :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ d :=
    DensePoly.gcd_dvd_right _ _
  -- `g ∣ r` via `g ∣ r/c ∣ r`.
  have hg_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨DensePoly.gcd r d * a, ?_⟩
    calc r
        = DensePoly.gcd r d * (r / DensePoly.gcd r d) := hr_eq
      _ = DensePoly.gcd r d *
            (DensePoly.gcd (r / DensePoly.gcd r d) d * a) := by
          exact congrArg (DensePoly.gcd r d * ·) ha
      _ = DensePoly.gcd (r / DensePoly.gcd r d) d *
            (DensePoly.gcd r d * a) :=
          fp_swap_left_mul _ _ _
  -- `g ∣ gcd r d = c`.
  have hg_dvd_c :
      DensePoly.gcd (r / DensePoly.gcd r d) d ∣ DensePoly.gcd r d :=
    DensePoly.dvd_gcd _ r d hg_dvd_r hg_dvd_d
  -- Hence `g * g ∣ r` (since `r = c * (r/c)` and `g ∣ c`, `g ∣ r/c`).
  have hg2_dvd_r :
      DensePoly.gcd (r / DensePoly.gcd r d) d *
        DensePoly.gcd (r / DensePoly.gcd r d) d ∣ r := by
    rcases hg_dvd_c with ⟨e, he⟩
    rcases hg_dvd_quot with ⟨a, ha⟩
    refine ⟨e * a, ?_⟩
    have hstep2 :
        DensePoly.gcd r d * (r / DensePoly.gcd r d) =
        (DensePoly.gcd (r / DensePoly.gcd r d) d * e) *
          (DensePoly.gcd (r / DensePoly.gcd r d) d * a) := by
      -- Use congrArg with two-argument function to avoid rw's recursive substitution.
      have h := congrArg
        (fun (xy : FpPoly p × FpPoly p) => xy.1 * xy.2)
        (Prod.ext he ha :
          (DensePoly.gcd r d, r / DensePoly.gcd r d) =
            (DensePoly.gcd (r / DensePoly.gcd r d) d * e,
             DensePoly.gcd (r / DensePoly.gcd r d) d * a))
      exact h
    exact hr_eq.trans (hstep2.trans
      (fp_swap_inner_mul (DensePoly.gcd (r / DensePoly.gcd r d) d) e a))
  exact isUnitPolynomial_of_squareFree_of_squared_dvd
    (squareFree_common_of_gcd_eq_one hsf) hg2_dvd_r

/-! ### Square-free divisor distribution across kernel-witness gcds

These lemmas package Step 3 of the Berlekamp completeness argument
(see `SPEC/Libraries/hex-berlekamp-mathlib.md`). Working from the
witness-level product/divisibility form `f ∣ Π_{c ∈ F_p} (w - C c)`,
they distribute the divisibility across the pairwise-coprime gcd
factors `gcd f (w - C c)`. Combined with a non-constancy hypothesis on
the witness (no single `(w - C c)` is divisible by `f`), this yields a
nontrivial Berlekamp split candidate.

The witness-level divisibility hypothesis is the caller-facing
interface; deriving it from `f ∣ FpPoly.linearPow w p - w` via the
prime-field product identity is tracked separately (see #4160). -/

omit [ZMod64.PrimeModulus p] in
/-- The difference of two distinct witness linear factors collapses to
the constant `C (d - c)`. -/
private theorem witnessLinearFactor_sub_eq
    (w : FpPoly p) (c d : ZMod64 p) :
    (w - FpPoly.C c) - (w - FpPoly.C d)
      = (DensePoly.C (d - c) : FpPoly p) := by
  apply DensePoly.ext_coeff
  intro n
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  rw [DensePoly.coeff_sub_ring]
  show w.coeff n - (FpPoly.C c).coeff n - (w.coeff n - (FpPoly.C d).coeff n)
    = (DensePoly.C (d - c) : FpPoly p).coeff n
  rw [show (FpPoly.C c).coeff n = (DensePoly.C c : FpPoly p).coeff n from rfl,
      show (FpPoly.C d).coeff n = (DensePoly.C d : FpPoly p).coeff n from rfl]
  rw [DensePoly.coeff_C, DensePoly.coeff_C, DensePoly.coeff_C]
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  rw [h0]
  by_cases hn : n = 0
  · simp [hn]; grind
  · simp [hn]; grind

/-- Distinct witness linear factors `(w - C c)` and `(w - C d)` are
coprime: their difference is a nonzero constant, so any common divisor
divides `1`. -/
theorem witnessLinearFactor_distinct_common_dvd_one
    {w : FpPoly p} {c d : ZMod64 p} (hcd : c ≠ d) (e : FpPoly p)
    (hec : e ∣ (w - FpPoly.C c))
    (hed : e ∣ (w - FpPoly.C d)) :
    e ∣ (1 : FpPoly p) := by
  have hdiff : e ∣ ((w - FpPoly.C c) - (w - FpPoly.C d)) :=
    DensePoly.dvd_sub_poly hec hed
  rw [witnessLinearFactor_sub_eq w c d] at hdiff
  have hdc_ne : (d - c) ≠ (0 : ZMod64 p) := by
    intro hzero
    apply hcd
    have : c = d := by grind
    exact this
  exact dvd_trans_local hdiff (C_ne_zero_dvd_one hdc_ne)

/-- Bezout-style cancellation through one witness linear factor: if `f`
divides `acc * (w - C c)` and `gcd(f, w - C c)` is a unit polynomial,
then `f ∣ acc`. -/
private theorem dvd_of_witness_mul_of_gcd_isUnit
    {f w acc : FpPoly p} {c : ZMod64 p}
    (hdvd : f ∣ acc * (w - FpPoly.C c))
    (hgcd : isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) :
    f ∣ acc := by
  have hdvd' : f ∣ (w - FpPoly.C c) * acc := by
    rw [FpPoly.mul_comm] at hdvd
    exact hdvd
  apply FpPoly.dvd_of_dvd_mul_of_common_dvd_one hdvd'
  intro d hd_lin hd_f
  exact dvd_one_of_isUnitPolynomial
    (isUnitPolynomial_of_dvd_isUnitPolynomial
      (DensePoly.dvd_gcd d f (w - FpPoly.C c) hd_f hd_lin) hgcd)

/-- Coprime-cancellation through the foldl shape of the witness product:
if every gcd `gcd(f, w - C c)` along the list `cs` is a unit polynomial,
then `f` divides the accumulator. -/
private theorem dvd_acc_of_foldl_witness_dvd_of_all_gcd_isUnit
    (f w : FpPoly p) :
    ∀ (cs : List (ZMod64 p)) (acc : FpPoly p),
      f ∣ cs.foldl (fun a c => a * (w - FpPoly.C c)) acc →
      (∀ c ∈ cs,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) →
      f ∣ acc := by
  intro cs
  induction cs with
  | nil =>
      intro acc hdvd _
      simpa using hdvd
  | cons c rest ih =>
      intro acc hdvd hcoprime
      simp only [List.foldl_cons] at hdvd
      have hcoprime_rest :
          ∀ c' ∈ rest,
            isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c')) = true :=
        fun c' hmem => hcoprime c' (List.mem_cons_of_mem _ hmem)
      have hdvd_step : f ∣ acc * (w - FpPoly.C c) :=
        ih _ hdvd hcoprime_rest
      exact dvd_of_witness_mul_of_gcd_isUnit hdvd_step
        (hcoprime c (List.mem_cons.mpr (Or.inl rfl)))

/-- If `f` divides the witness product and every witness gcd is a unit,
then `f ∣ 1`. -/
private theorem dvd_one_of_witnessProduct_dvd_of_all_gcd_isUnit
    {f w : FpPoly p}
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hgcd :
      ∀ c : ZMod64 p,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true) :
    f ∣ (1 : FpPoly p) :=
  dvd_acc_of_foldl_witness_dvd_of_all_gcd_isUnit f w (ZMod64.values p) 1 hdvd
    (fun c _ => hgcd c)

/-- If `f` has positive degree, then `gcd(f, a)` is nonzero for any `a`. -/
private theorem gcd_isZero_false_of_left_pos_degree
    {f : FpPoly p} (a : FpPoly p) (hf_pos : 0 < f.degree?.getD 0) :
    (DensePoly.gcd f a).isZero = false := by
  have hf_ne : f ≠ 0 := ne_zero_of_pos_degree hf_pos
  cases hg : (DensePoly.gcd f a).isZero with
  | false => rfl
  | true =>
      exfalso
      apply hf_ne
      have hg_zero : DensePoly.gcd f a = 0 := by
        apply DensePoly.ext_coeff
        intro n
        have hsize : (DensePoly.gcd f a).size = 0 := by
          simpa [DensePoly.isZero, DensePoly.size,
            Array.isEmpty_iff_size_eq_zero] using hg
        rw [DensePoly.coeff_eq_zero_of_size_le _ (by omega : (DensePoly.gcd f a).size ≤ n),
          DensePoly.coeff_zero]
        rfl
      rcases DensePoly.gcd_dvd_left f a with ⟨q, hq⟩
      rw [hq, hg_zero, FpPoly.zero_mul]

/-- Square-free divisor distribution (non-unit existence): if `f` has
positive degree and divides the canonical witness product over `F_p`,
some `gcd(f, w - C c)` is non-unit. This is the coprime-cancellation
core of Step 3, working purely from the divisibility hypothesis. -/
theorem exists_gcd_not_isUnit_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1) :
    ∃ c : ZMod64 p,
      isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = false := by
  apply Classical.byContradiction
  intro hno
  have hcoprime :
      ∀ c : ZMod64 p,
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true := by
    intro c
    cases hC : isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) with
    | true => rfl
    | false => exact absurd ⟨c, hC⟩ hno
  have hf_dvd_one : f ∣ (1 : FpPoly p) :=
    dvd_one_of_witnessProduct_dvd_of_all_gcd_isUnit hdvd hcoprime
  have hf_unit : isUnitPolynomial f = true :=
    isUnitPolynomial_of_dvd_isUnitPolynomial hf_dvd_one isUnitPolynomial_one_FpPoly
  have hf_not_unit : isUnitPolynomial f = false :=
    isUnitPolynomial_eq_false_of_pos_degree hf_pos
  rw [hf_not_unit] at hf_unit
  exact Bool.noConfusion hf_unit

/-- Square-free divisor distribution (nontrivial split): under the
non-constancy hypothesis that no single `(w - C c)` is divisible by `f`,
some witness gcd is nonzero, nonconstant, and not equal to `f`. This is
the form consumed by the executable Berlekamp split surface (see
`HexBerlekamp.Berlekamp.kernelWitnessSplit?_some_of_nontrivial_splitFactorAt`).

`f` does not need to be square-free for this statement; the deliverable
shape exposes the square-freeness hypothesis at the call site, where
the witness-level divisibility hypothesis itself is derived from
square-freeness (#4160). -/
theorem exists_nontrivial_gcd_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hnonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c))) :
    ∃ c : ZMod64 p,
      (DensePoly.gcd f (w - FpPoly.C c)).isZero = false ∧
      (DensePoly.gcd f (w - FpPoly.C c)).degree? ≠ some 0 ∧
      DensePoly.gcd f (w - FpPoly.C c) ≠ f := by
  obtain ⟨c, hnotUnit⟩ :=
    exists_gcd_not_isUnit_of_witnessProduct_dvd_of_pos_degree hf_pos hdvd
  refine ⟨c, gcd_isZero_false_of_left_pos_degree _ hf_pos, ?_, ?_⟩
  · intro hdeg
    have hunit :
        isUnitPolynomial (DensePoly.gcd f (w - FpPoly.C c)) = true := by
      unfold isUnitPolynomial
      rw [hdeg]
    rw [hunit] at hnotUnit
    exact Bool.noConfusion hnotUnit
  · intro hgcd_eq_f
    apply hnonconst c
    rw [← hgcd_eq_f]
    exact DensePoly.gcd_dvd_right f (w - FpPoly.C c)

/--
Executable composition of the square-free distribution step: once the
witness-product divisibility hypothesis is available and the witness is not
constant modulo `f`, the Berlekamp split search finds a concrete split result.

The upstream derivation of `hdvd` from a fixed-space/kernel hypothesis is kept
separate; this theorem only packages the local distribution result with the
executable search reflection.
-/
theorem exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree
    {f w : FpPoly p}
    (hf_pos : 0 < f.degree?.getD 0)
    (hdvd : f ∣ (ZMod64.values p).foldl
        (fun acc c => acc * (w - FpPoly.C c)) 1)
    (hnonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c))) :
    ∃ r : SplitResult p, kernelWitnessSplit? f w = some r := by
  obtain ⟨c, hnotZero, hdegree, _hne_input⟩ :=
    exists_nontrivial_gcd_of_witnessProduct_dvd_of_pos_degree hf_pos hdvd hnonconst
  have hsize_lt : (DensePoly.gcd f (w - FpPoly.C c)).size < f.size := by
    have hf_ne : f ≠ 0 := ne_zero_of_pos_degree hf_pos
    have hgcd_dvd_f : DensePoly.gcd f (w - FpPoly.C c) ∣ f :=
      DensePoly.gcd_dvd_left _ _
    have hgcd_dvd_h : DensePoly.gcd f (w - FpPoly.C c) ∣ (w - FpPoly.C c) :=
      DensePoly.gcd_dvd_right _ _
    apply Classical.byContradiction
    intro hge
    have hge : f.size ≤ (DensePoly.gcd f (w - FpPoly.C c)).size := Nat.le_of_not_lt hge
    have hsize_le : (DensePoly.gcd f (w - FpPoly.C c)).size ≤ f.size :=
      FpPoly.size_le_of_dvd_of_ne_zero hgcd_dvd_f hf_ne
    have hquot_size : (f / DensePoly.gcd f (w - FpPoly.C c)).size = 1 := by
      have hsplit :=
        FpPoly.size_div_add_size_eq_size_add_one_of_dvd hgcd_dvd_f hf_ne
      omega
    have hquot_unit :
        isUnitPolynomial (f / DensePoly.gcd f (w - FpPoly.C c)) = true := by
      unfold isUnitPolynomial
      have hquot_deg : (f / DensePoly.gcd f (w - FpPoly.C c)).degree? = some 0 := by
        unfold DensePoly.degree?
        simp [hquot_size]
      rw [hquot_deg]
    have hquot_dvd_one :
        (f / DensePoly.gcd f (w - FpPoly.C c)) ∣ (1 : FpPoly p) :=
      dvd_one_of_isUnitPolynomial hquot_unit
    rcases hquot_dvd_one with ⟨e, he⟩
    have hf_eq :
        f = DensePoly.gcd f (w - FpPoly.C c) *
            (f / DensePoly.gcd f (w - FpPoly.C c)) :=
      fp_eq_mul_div_of_dvd hgcd_dvd_f
    have hke : (f / DensePoly.gcd f (w - FpPoly.C c)) * e = 1 := he.symm
    have hf_dvd_gcd : f ∣ DensePoly.gcd f (w - FpPoly.C c) := by
      refine ⟨e, ?_⟩
      calc DensePoly.gcd f (w - FpPoly.C c)
          = DensePoly.gcd f (w - FpPoly.C c) * 1 :=
            (DensePoly.mul_one_right_poly _).symm
        _ = DensePoly.gcd f (w - FpPoly.C c) *
              ((f / DensePoly.gcd f (w - FpPoly.C c)) * e) := by rw [hke]
        _ = (DensePoly.gcd f (w - FpPoly.C c) *
              (f / DensePoly.gcd f (w - FpPoly.C c))) * e :=
            (FpPoly.mul_assoc _ _ _).symm
        _ = f * e := by rw [← hf_eq]
    exact hnonconst c (fp_dvd_trans hf_dvd_gcd hgcd_dvd_h)
  exact kernelWitnessSplit?_some_of_nontrivial_splitFactorAt f w c
    (by simp [splitFactorAt, hnotZero])
    (by simpa [splitFactorAt] using hdegree)
    (by simpa [splitFactorAt] using hsize_lt)

/-! ### Bezout-coefficient route for square-free monic splits

From any nontrivial product factorization of a square-free monic `f`, the
common-divisor form `gcd a b ∣ 1` supplied by `common_dvd_one_of_squareFree_mul`
scales the xgcd Bezout identity to `s * a + t * b = 1`. This bypasses the
`Monic (DensePoly.gcd a b)` hypothesis required by the corresponding
`_squareFree_split` wrapper, by using explicit Bezout coefficients to feed
`crtZeroOneCandidate` directly. -/

/-- From `gcd a b ∣ 1`, scale the xgcd Bezout identity by the cofactor of `1`
to obtain explicit `s, t` with `s * a + t * b = 1`. -/
private theorem exists_bezout_eq_one_of_gcd_dvd_one
    (a b : FpPoly p) (hgcd_dvd : DensePoly.gcd a b ∣ (1 : FpPoly p)) :
    ∃ s t : FpPoly p, s * a + t * b = 1 := by
  rcases hgcd_dvd with ⟨e, he⟩
  have hbez_raw :
      (DensePoly.xgcd a b).left * a + (DensePoly.xgcd a b).right * b =
        (DensePoly.xgcd a b).gcd := by
    simpa using DensePoly.xgcd_bezout a b
  have hxgcd_eq : (DensePoly.xgcd a b).gcd = DensePoly.gcd a b := rfl
  refine ⟨e * (DensePoly.xgcd a b).left, e * (DensePoly.xgcd a b).right, ?_⟩
  calc
    e * (DensePoly.xgcd a b).left * a + e * (DensePoly.xgcd a b).right * b
        = e * ((DensePoly.xgcd a b).left * a) +
            e * ((DensePoly.xgcd a b).right * b) := by
          rw [FpPoly.mul_assoc e (DensePoly.xgcd a b).left a,
              FpPoly.mul_assoc e (DensePoly.xgcd a b).right b]
      _ = e * ((DensePoly.xgcd a b).left * a +
              (DensePoly.xgcd a b).right * b) :=
          (FpPoly.left_distrib e _ _).symm
      _ = e * (DensePoly.xgcd a b).gcd := by rw [hbez_raw]
      _ = e * DensePoly.gcd a b := by rw [hxgcd_eq]
      _ = DensePoly.gcd a b * e := FpPoly.mul_comm _ _
      _ = 1 := he.symm

omit [ZMod64.PrimeModulus p] in
/-- The common-divisor form `∀ d, d ∣ a → d ∣ b → d ∣ 1` is also a consequence
of an explicit `s * a + t * b = 1` Bezout identity, with no monicity required
on the gcd. -/
private theorem common_dvd_one_of_bezout
    {a b s t : FpPoly p}
    (hbez : s * a + t * b = 1) (d : FpPoly p)
    (hda : d ∣ a) (hdb : d ∣ b) : d ∣ (1 : FpPoly p) := by
  rcases hda with ⟨a', ha'⟩
  rcases hdb with ⟨b', hb'⟩
  refine ⟨s * a' + t * b', ?_⟩
  have hs : s * (d * a') = d * (s * a') := by
    calc s * (d * a')
        = (s * d) * a' := (FpPoly.mul_assoc s d a').symm
      _ = (d * s) * a' := by rw [FpPoly.mul_comm s d]
      _ = d * (s * a') := FpPoly.mul_assoc d s a'
  have ht : t * (d * b') = d * (t * b') := by
    calc t * (d * b')
        = (t * d) * b' := (FpPoly.mul_assoc t d b').symm
      _ = (d * t) * b' := by rw [FpPoly.mul_comm t d]
      _ = d * (t * b') := FpPoly.mul_assoc d t b'
  calc 1
      = s * a + t * b := hbez.symm
    _ = s * (d * a') + t * (d * b') := by rw [ha', hb']
    _ = d * (s * a') + d * (t * b') := by rw [hs, ht]
    _ = d * (s * a' + t * b') := (FpPoly.left_distrib d _ _).symm

/-- Reduced zero-one CRT witness from explicit Bezout coefficients. Parallels
`exists_reduced_crtZeroOne_kernelWitness_of_coprime_split` but consumes an
arbitrary Bezout pair `s * a + t * b = 1` instead of `gcd a b = 1`. -/
private theorem exists_reduced_crtZeroOne_kernelWitness_of_bezout
    (a b s t : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hbez : s * a + t * b = 1) :
    ∃ h : FpPoly p,
      h = crtZeroOneCandidate a b s t % (a * b) ∧
      (a * b) ∣ (FpPoly.linearPow h p - h) ∧
      ∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b) := by
  let h0 := crtZeroOneCandidate a b s t
  refine ⟨h0 % (a * b), rfl, ?_, ?_⟩
  · have hleft : a ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_zero a h0
        (crtZeroOneCandidate_congr_zero_left a b s t hbez)
    have hright : b ∣ (FpPoly.linearPow h0 p - h0) :=
      dvd_linearPow_sub_self_of_congr_one b h0
        (crtZeroOneCandidate_congr_one_right a b s t hbez)
    have hprod : a * b ∣ (FpPoly.linearPow h0 p - h0) :=
      mul_dvd_of_dvd_dvd_common hleft hright (common_dvd_one_of_bezout hbez)
    have hred :=
      (dvd_linearPow_sub_self_mod_iff (a * b) h0 1).mp (by simpa using hprod)
    simpa using hred
  · intro c
    apply not_congr_constant_mod_of_mod (a * b) h0 c
    exact crtZeroOneCandidate_not_congr_constant_mod_product a b s t
      ha hb ha_pos hb_pos hbez c

/-- Reduced zero-one CRT witness for a monic split of a square-free product.
Avoids the `Monic (DensePoly.gcd a b)` hypothesis of
`exists_reduced_crtZeroOne_kernelWitness_of_squareFree_split` by routing
through `common_dvd_one_of_squareFree_mul` and the Bezout-coefficient route.
-/
private theorem exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split
    (a b : FpPoly p)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b)
    (ha_pos : 0 < a.degree?.getD 0) (hb_pos : 0 < b.degree?.getD 0)
    (hsf : ∀ d, d ∣ (a * b) → d ∣ DensePoly.derivative (a * b) →
      isUnitPolynomial d = true) :
    ∃ h : FpPoly p,
      (a * b) ∣ (FpPoly.linearPow h p - h) ∧
      (∀ c : ZMod64 p, ¬ DensePoly.Congr h (DensePoly.C c) (a * b)) ∧
      h.size ≤ (a * b).degree?.getD 0 := by
  have hgcd_dvd_one : DensePoly.gcd a b ∣ (1 : FpPoly p) :=
    common_dvd_one_of_squareFree_mul hsf
      (DensePoly.gcd_dvd_left a b) (DensePoly.gcd_dvd_right a b)
  obtain ⟨s, t, hbez⟩ := exists_bezout_eq_one_of_gcd_dvd_one a b hgcd_dvd_one
  obtain ⟨h, hheq, hdvd, hnonconst⟩ :=
    exists_reduced_crtZeroOne_kernelWitness_of_bezout
      a b s t ha hb ha_pos hb_pos hbez
  refine ⟨h, hdvd, hnonconst, ?_⟩
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  have hab_pos : 0 < (a * b).degree?.getD 0 := by
    have ha_ne : a ≠ 0 := ne_zero_of_pos_degree ha_pos
    have hb_ne : b ≠ 0 := ne_zero_of_pos_degree hb_pos
    rw [FpPoly.degree?_mul_eq_add_degree? a b ha_ne hb_ne]
    omega
  rw [hheq]
  have hlt :=
    DensePoly.mod_degree_lt_of_pos_degree
      (crtZeroOneCandidate a b s t) (a * b) hab_pos
  by_cases hsize :
      (crtZeroOneCandidate a b s t % (a * b)).size = 0
  · omega
  · have hpos :
        0 < (crtZeroOneCandidate a b s t % (a * b)).size :=
      Nat.pos_of_ne_zero hsize
    have hdeg_eq :
        (crtZeroOneCandidate a b s t % (a * b)).degree?.getD 0 =
          (crtZeroOneCandidate a b s t % (a * b)).size - 1 := by
      unfold DensePoly.degree?
      simp [Nat.ne_of_gt hpos]
    omega

/-! ### Berlekamp completeness composition

Combining the CRT-produced kernel polynomial with the matrix-kernel iff
yields the algebraic half of Berlekamp completeness: if no fixed-space
kernel witness admits a Berlekamp split, the square-free monic input is
irreducible. -/

omit [ZMod64.PrimeModulus p] in
/-- Foldl of zero terms over `ZMod64 p` starting from `0` stays at `0`. -/
private theorem foldl_add_eq_zero_of_terms_zero
    {α : Type _} (xs : List α) (g : α → ZMod64 p)
    (hg : ∀ x ∈ xs, g x = 0) :
    xs.foldl (fun acc x => acc + g x) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : g x = 0 := hg x (by simp)
      have hxs : ∀ y ∈ xs, g y = 0 := fun y hy => hg y (List.mem_cons_of_mem _ hy)
      have hzero_add : (0 : ZMod64 p) + g x = 0 := by rw [hx]; grind
      rw [hzero_add]
      exact ih hxs

/-- Relate a `nullspaceBasisMatrix` entry to the corresponding basis polynomial
coefficient. The `(i, k)` entry of the basis matrix equals the `i`-th coefficient
of the `k`-th basis polynomial, for `i < basisSize f`. -/
private theorem nullspaceBasisMatrix_entry_eq_basis_coeff
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (k : Fin (basisSize f -
      Matrix.rref_rank (fixedSpaceMatrix f hmonic)))
    (i : Nat) (hi : i < basisSize f) :
    ((Matrix.nullspaceBasisMatrix (fixedSpaceMatrix f hmonic))[i]'hi)[k.val]'k.isLt =
      ((fixedSpaceKernel f hmonic).get k).coeff i := by
  -- Establish: ((fixedSpaceKernel f hmonic).get k).coeff i = coeffVector f (basis k) [i]
  have hker_coeff :
      ((fixedSpaceKernel f hmonic).get k).coeff i =
        (coeffVector f ((fixedSpaceKernel f hmonic).get k))[i]'hi := by
    unfold coeffVector
    rw [Vector.getElem_ofFn]
  -- coeffVector f (basis k) = (fixedSpaceKernelVectors f hmonic).get k
  have hker_eq :
      coeffVector f ((fixedSpaceKernel f hmonic).get k) =
        (fixedSpaceKernelVectors f hmonic).get k := by
    unfold fixedSpaceKernel
    rw [Vector.get_ofFn, coeffVector_vectorToPoly]
  rw [hker_coeff, hker_eq]
  -- Goal: M'[i][k.val] = ((fixedSpaceKernelVectors f hmonic).get k)[i]
  -- Express both sides through the shared `rref_isRREF` instance.
  let E := Matrix.rref_isRREF (fixedSpaceMatrix f hmonic)
  show (E.nullspaceMatrix[i]'hi)[k.val]'k.isLt = (E.nullspace.get k)[i]'hi
  unfold Matrix.IsRREF.nullspace
  rw [Vector.get_ofFn]
  unfold Matrix.col
  rw [Vector.getElem_ofFn]
  rfl

/--
**Algebraic half of Berlekamp completeness for square-free inputs.**

For a monic square-free `f ∈ F_p[x]`, if every fixed-space kernel witness fails
to produce a Berlekamp split (`kernelWitnessSplit? f w = none`), then `f` is
irreducible.

The proof goes by contradiction: a nontrivial factorization `f = a₀ * b₀`
yields a monic irreducible factor `g ∣ a₀` and a monic cofactor `b' = f / g`
of positive degree. The reduced CRT zero-one witness from
`exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split` produces
a polynomial `h` of size `≤ basisSize f` with `f ∣ linearPow h p - h` and
`h` nonconstant modulo `f`. The fixed-space iff
(`isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self`) makes `h` an
algebraic kernel polynomial; the spanning lemma
`fixedSpaceKernelPolynomial_coeffVector_complete` decomposes its coefficient
vector as a linear combination of basis polynomials. Because `h` is not a
constant, at least one basis polynomial `w` must be nonconstant; the iff in
the matrix→algebraic direction (`fixedSpaceKernel_sound`) and
`dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self` lift `w` to a
witness of `f ∣ Π_c (w − C c)`. The executable split surface
`exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree` then
produces `kernelWitnessSplit? f w = some _`, contradicting `hno_split`.
-/
theorem irreducible_of_no_kernelWitnessSplit_squareFree
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hno_split : ∀ w ∈ (fixedSpaceKernel f hmonic).toList,
      kernelWitnessSplit? f w = none) :
    FpPoly.Irreducible f := by
  haveI : DensePoly.DivModLaws (ZMod64 p) := ZMod64.instDivModLawsZMod64Fp p
  -- f ≠ 0 from monicity.
  have hf_ne_zero : f ≠ 0 := by
    intro hzero
    have hlead : f.leadingCoeff = 1 := hmonic
    rw [hzero] at hlead
    have hlead_zero : (0 : FpPoly p).leadingCoeff = 0 := by
      change (0 : FpPoly p).coeffs.back?.getD 0 = 0
      have hcoeffs : (0 : FpPoly p).coeffs = #[] := rfl
      rw [hcoeffs]; rfl
    rw [hlead_zero] at hlead
    exact zmod64_one_ne_zero_local hlead.symm
  refine ⟨hf_ne_zero, ?_⟩
  intro a₀ b₀ hab
  by_cases ha₀_unit : a₀.degree? = some 0
  · exact Or.inl ha₀_unit
  refine Or.inr ?_
  by_cases hb₀_unit : b₀.degree? = some 0
  · exact hb₀_unit
  exfalso
  -- Both factors are nonconstant.
  have ha₀_ne_zero : a₀ ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb₀_ne_zero : b₀ ≠ 0 := by
    have hba : b₀ * a₀ = f := by rw [FpPoly.mul_comm]; exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha₀_pos : 0 < a₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit ha₀_ne_zero ha₀_unit
  have hb₀_pos : 0 < b₀.degree?.getD 0 :=
    pos_degree_of_ne_zero_of_not_isUnit hb₀_ne_zero hb₀_unit
  have ha₀_lt_f : a₀.degree?.getD 0 < basisSize f :=
    factor_degree_lt_basisSize hab ha₀_ne_zero hb₀_pos
  -- Extract a monic irreducible factor `g` of `a₀`.
  obtain ⟨g, _hg_irr, hg_monic, hg_dvd_a₀, hg_deg_pos, hg_deg_le_a₀⟩ :=
    exists_monic_irreducible_factor_of_factor hmonic hab ha₀_pos
  -- `g ∣ f` via `g ∣ a₀ ∣ f`.
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a₀ with ⟨r, hr⟩
    refine ⟨r * b₀, ?_⟩
    calc f = a₀ * b₀ := hab.symm
      _ = (g * r) * b₀ := by rw [hr]
      _ = g * (r * b₀) := FpPoly.mul_assoc g r b₀
  have hg_ne_zero : g ≠ 0 := ne_zero_of_pos_degree hg_deg_pos
  -- Cofactor `b' := f / g` with `g * b' = f`.
  let b' : FpPoly p := f / g
  have hf_eq : g * b' = f := (fp_eq_mul_div_of_dvd hg_dvd_f).symm
  have hb'_ne_zero : b' ≠ 0 := by
    intro hzero
    rw [hzero, FpPoly.mul_zero] at hf_eq
    exact hf_ne_zero hf_eq.symm
  -- `b'` is monic: leading coefficient is forced by `g * b' = f` and both `g, f` monic.
  have hb'_monic : DensePoly.Monic b' := by
    have hlead : DensePoly.leadingCoeff f =
        DensePoly.leadingCoeff g * DensePoly.leadingCoeff b' := by
      rw [← hf_eq]
      exact leadingCoeff_mul_fpoly g b' hg_ne_zero hb'_ne_zero
    have hf_one : DensePoly.leadingCoeff f = 1 := hmonic
    have hg_one : DensePoly.leadingCoeff g = 1 := hg_monic
    unfold DensePoly.Monic
    rw [hg_one, hf_one] at hlead
    have hone_mul : (1 : ZMod64 p) * DensePoly.leadingCoeff b' =
        DensePoly.leadingCoeff b' := by grind
    rw [hone_mul] at hlead
    exact hlead.symm
  -- `b'` has positive degree.
  have hg_lt_f : g.degree?.getD 0 < basisSize f :=
    Nat.lt_of_le_of_lt hg_deg_le_a₀ ha₀_lt_f
  have hb'_pos : 0 < b'.degree?.getD 0 := by
    have hdeg_eq : (g * b').degree?.getD 0 =
        g.degree?.getD 0 + b'.degree?.getD 0 :=
      FpPoly.degree?_mul_eq_add_degree? g b' hg_ne_zero hb'_ne_zero
    rw [hf_eq] at hdeg_eq
    unfold basisSize at hg_lt_f
    omega
  -- Square-freeness on `g * b' = f`.
  have hsf' : ∀ d, d ∣ (g * b') → d ∣ DensePoly.derivative (g * b') →
      isUnitPolynomial d = true := by
    rw [hf_eq]; exact hsquareFree
  -- Reduced zero-one CRT witness `h`.
  obtain ⟨h, h_dvd, h_nonconst, h_size⟩ :=
    exists_reduced_crtZeroOne_kernelWitness_of_squareFree_monic_split
      g b' hg_monic hb'_monic hg_deg_pos hb'_pos hsf'
  rw [hf_eq] at h_dvd h_nonconst h_size
  -- Size bound: `h.size ≤ basisSize f`.
  have hh_size_le : h.size ≤ basisSize f := h_size
  -- `h` is a fixed-space kernel polynomial.
  have hh_kernel : IsFixedSpaceKernelPolynomial f hmonic h := by
    rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self f hmonic h hh_size_le]
    exact h_dvd
  -- Span as linear combination of basis vectors.
  obtain ⟨c_coeff, hc_eq⟩ :=
    fixedSpaceKernelPolynomial_coeffVector_complete f hmonic h hh_kernel
  -- Notation for the basis matrix.
  let M := fixedSpaceMatrix f hmonic
  -- Set kernel dimension shorthand.
  let ndim := basisSize f - Matrix.rref_rank M
  -- Extract a nonconstant basis polynomial, contradicting `hno_split`.
  -- Strategy: if every basis polynomial is a constant, then h is a constant,
  -- contradicting h_nonconst applied to h.coeff 0.
  have hbasis_size_le : ∀ k : Fin ndim,
      ((fixedSpaceKernel f hmonic).get k).size ≤ basisSize f := by
    intro k
    have hker_eq :
        (fixedSpaceKernel f hmonic).get k =
          vectorToPoly ((fixedSpaceKernelVectors f hmonic).get k) := by
      unfold fixedSpaceKernel
      rw [Vector.get_ofFn]
    rw [hker_eq]
    unfold vectorToPoly
    have hle :
        (FpPoly.ofCoeffs
            ((fixedSpaceKernelVectors f hmonic).get k).toArray).size ≤
          ((fixedSpaceKernelVectors f hmonic).get k).toArray.size :=
      DensePoly.size_ofCoeffs_le _
    have hsz :
        ((fixedSpaceKernelVectors f hmonic).get k).toArray.size = basisSize f :=
      ((fixedSpaceKernelVectors f hmonic).get k).size_toArray
    omega
  by_cases hall_const :
      ∀ k : Fin ndim, ((fixedSpaceKernel f hmonic).get k).size ≤ 1
  · -- Every basis polynomial is a constant. Show `h` is a constant.
    -- Specifically, prove `h.coeff i = 0` for all `i ≥ 1`.
    have hh_coeff_zero : ∀ i, 1 ≤ i → h.coeff i = 0 := by
      intro i hi
      by_cases hi_lt : i < basisSize f
      · -- Use hc_eq to extract h.coeff i as a linear combination.
        have hi_fin : i < basisSize f := hi_lt
        have hget :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix M) c_coeff)[i]'hi_fin =
              (coeffVector f h)[i]'hi_fin :=
          congrArg (fun v : Vector (ZMod64 p) (basisSize f) => v[i]'hi_fin) hc_eq
        -- Right-hand side is h.coeff i.
        have hrhs : (coeffVector f h)[i]'hi_fin = h.coeff i := by
          unfold coeffVector
          rw [Vector.getElem_ofFn hi_fin]
        -- Left-hand side expands to a foldl.
        have hlhs :
            (Matrix.mulVec (Matrix.nullspaceBasisMatrix M) c_coeff)[i]'hi_fin =
              (List.finRange ndim).foldl
                (fun acc k => acc +
                  ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                    c_coeff[k.val]'k.isLt) 0 := by
          unfold Matrix.mulVec Matrix.dot Hex.Vector.dotProduct Matrix.row
          rw [Vector.getElem_ofFn hi_fin]
          rfl
        rw [hlhs] at hget
        rw [hrhs] at hget
        -- All terms in the foldl are 0 because basis polynomials have size ≤ 1.
        have hzero_terms : ∀ k ∈ List.finRange ndim,
            ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                c_coeff[k.val]'k.isLt = 0 := by
          intro k _hk
          rw [nullspaceBasisMatrix_entry_eq_basis_coeff f hmonic k i hi_fin]
          have hk_const : ((fixedSpaceKernel f hmonic).get k).size ≤ 1 := hall_const k
          have hcoeff_zero : ((fixedSpaceKernel f hmonic).get k).coeff i = 0 :=
            DensePoly.coeff_eq_zero_of_size_le _ (by omega)
          rw [hcoeff_zero]
          grind
        have hfoldl_zero :
            (List.finRange ndim).foldl
              (fun acc k => acc +
                ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
                  c_coeff[k.val]'k.isLt) 0 = 0 :=
          foldl_add_eq_zero_of_terms_zero (List.finRange ndim)
            (fun k => ((Matrix.nullspaceBasisMatrix M)[i]'hi_fin)[k.val]'k.isLt *
              c_coeff[k.val]'k.isLt)
            hzero_terms
        rw [hfoldl_zero] at hget
        exact hget.symm
      · have hi_ge : basisSize f ≤ i := Nat.le_of_not_lt hi_lt
        exact DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_trans hh_size_le hi_ge)
    -- `h = DensePoly.C d` for a fresh `d`.
    have hh_eq_C : ∃ d : ZMod64 p, h = DensePoly.C d := by
      refine ⟨h.coeff 0, ?_⟩
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_C]
      cases i with
      | zero => simp
      | succ i =>
          rw [hh_coeff_zero (i + 1) (by omega)]
          simp; rfl
    obtain ⟨d, hd⟩ := hh_eq_C
    -- Then `f ∣ h - C d` holds (the difference is 0).
    apply h_nonconst d
    refine ⟨0, ?_⟩
    rw [hd, FpPoly.sub_self, FpPoly.mul_zero]
  · -- Some basis polynomial is nonconstant. Use it to contradict hno_split.
    obtain ⟨k, hk⟩ := Classical.not_forall.mp hall_const
    let w : FpPoly p := (fixedSpaceKernel f hmonic).get k
    have hw_size_ge : 1 < w.size := Nat.lt_of_not_le hk
    -- w is in the kernel toList.
    have hw_mem : w ∈ (fixedSpaceKernel f hmonic).toList := by
      have hk_lt :
          k.val < (fixedSpaceKernel f hmonic).toList.length := by
        rw [Vector.length_toList]
        exact k.isLt
      have hget :
          (fixedSpaceKernel f hmonic).toList[k.val]'hk_lt = w := by
        rw [Vector.getElem_toList]
        rfl
      rw [← hget]
      exact List.getElem_mem hk_lt
    -- w is a kernel polynomial.
    have hw_kernel : IsFixedSpaceKernelPolynomial f hmonic w :=
      fixedSpaceKernel_sound f hmonic k
    -- w has size ≤ basisSize f.
    have hw_size_le : w.size ≤ basisSize f := hbasis_size_le k
    -- Hence f ∣ linearPow w p - w.
    have hw_dvd : f ∣ FpPoly.linearPow w p - w := by
      rw [isFixedSpaceKernelPolynomial_iff_dvd_linearPow_sub_self
        f hmonic w hw_size_le] at hw_kernel
      exact hw_kernel
    -- Apply prime-field product identity.
    have hw_prod :
        f ∣ (ZMod64.values p).foldl
          (fun acc c => acc * (w - FpPoly.C c)) 1 :=
      dvd_primeFieldProduct_witness_of_dvd_linearPow_sub_self hw_dvd
    -- w is not congruent to any constant modulo f.
    have hbasis_pos : 0 < basisSize f := by
      have hgpos : 0 < g.degree?.getD 0 := hg_deg_pos
      omega
    have hw_nonconst : ∀ c : ZMod64 p, ¬ (f ∣ (w - FpPoly.C c)) := by
      intro c hc
      -- (w - C c) ≠ 0 because its leading coefficient at index (w.size - 1) is nonzero.
      have hw_lead : w.coeff (w.size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size w (by omega)
      have hC_coeff_high : (FpPoly.C c).coeff (w.size - 1) = 0 := by
        change (DensePoly.C c).coeff (w.size - 1) = 0
        rw [DensePoly.coeff_C]
        have : w.size - 1 ≠ 0 := by omega
        simp [this]; rfl
      have hsub_at_top : (w - FpPoly.C c).coeff (w.size - 1) =
          w.coeff (w.size - 1) - (FpPoly.C c).coeff (w.size - 1) := by
        rw [DensePoly.coeff_sub_ring]
      have hsub_top_ne : (w - FpPoly.C c).coeff (w.size - 1) ≠ 0 := by
        rw [hsub_at_top, hC_coeff_high]
        intro hzero
        apply hw_lead
        have hsubzero : w.coeff (w.size - 1) - (0 : ZMod64 p) =
            w.coeff (w.size - 1) := by grind
        rw [hsubzero] at hzero
        exact hzero
      have hwc_ne_zero : w - FpPoly.C c ≠ 0 := by
        intro hwc_zero
        apply hsub_top_ne
        rw [hwc_zero]
        change (0 : FpPoly p).coeff (w.size - 1) = 0
        rw [DensePoly.coeff_zero]
        rfl
      -- (w - C c).size ≤ basisSize f via coefficient analysis above basisSize f.
      have hwc_size_le : (w - FpPoly.C c).size ≤ basisSize f := by
        apply Classical.byContradiction
        intro hgt
        have hgt : basisSize f < (w - FpPoly.C c).size := Nat.lt_of_not_le hgt
        have hwc_pos : 0 < (w - FpPoly.C c).size := by omega
        have hidx_ge : basisSize f ≤ (w - FpPoly.C c).size - 1 := by omega
        have hlast_ne :
            (w - FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) ≠ 0 :=
          DensePoly.coeff_last_ne_zero_of_pos_size _ hwc_pos
        have hw_zero_top :
            w.coeff ((w - FpPoly.C c).size - 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le _ (Nat.le_trans hw_size_le hidx_ge)
        have hC_zero_top :
            (FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) = 0 := by
          change (DensePoly.C c).coeff ((w - FpPoly.C c).size - 1) = 0
          rw [DensePoly.coeff_C]
          have hne : (w - FpPoly.C c).size - 1 ≠ 0 := by omega
          simp [hne]; rfl
        have hsub_top :
            (w - FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) =
              w.coeff ((w - FpPoly.C c).size - 1) -
                (FpPoly.C c).coeff ((w - FpPoly.C c).size - 1) := by
          rw [DensePoly.coeff_sub_ring]
        rw [hsub_top, hw_zero_top, hC_zero_top] at hlast_ne
        apply hlast_ne
        change (0 : ZMod64 p) - (0 : ZMod64 p) = 0
        grind
      -- (w - C c).degree < basisSize f, so (w - C c) % f = (w - C c).
      have hwc_deg_lt : (w - FpPoly.C c).degree?.getD 0 < basisSize f := by
        by_cases hsize : (w - FpPoly.C c).size = 0
        · -- (w - C c) = 0, contradicting hwc_ne_zero.
          exfalso
          apply hwc_ne_zero
          apply DensePoly.ext_coeff
          intro i
          rw [DensePoly.coeff_zero]
          exact DensePoly.coeff_eq_zero_of_size_le _ (by omega)
        · have hsize_pos : 0 < (w - FpPoly.C c).size := Nat.pos_of_ne_zero hsize
          have hdeg : (w - FpPoly.C c).degree? =
              some ((w - FpPoly.C c).size - 1) := by
            unfold DensePoly.degree?
            simp [hsize]
          rw [hdeg]
          simp
          omega
      have hwc_mod_self : (w - FpPoly.C c) % f = (w - FpPoly.C c) := by
        apply DensePoly.mod_eq_self_of_degree_lt
        change _ < basisSize f
        exact hwc_deg_lt
      have hwc_mod_zero : (w - FpPoly.C c) % f = 0 :=
        DensePoly.mod_eq_zero_of_dvd _ _ hc
      rw [hwc_mod_self] at hwc_mod_zero
      exact hwc_ne_zero hwc_mod_zero
    -- Now apply the executable split.
    have hf_pos : 0 < f.degree?.getD 0 := by
      have : 0 < basisSize f := hbasis_pos
      unfold basisSize at this
      exact this
    obtain ⟨r, hsplit⟩ :=
      exists_kernelWitnessSplit?_some_of_witnessProduct_dvd_of_pos_degree
        hf_pos hw_prod hw_nonconst
    have hno_w : kernelWitnessSplit? f w = none := hno_split w hw_mem
    rw [hno_w] at hsplit
    nomatch hsplit

/--
For a monic square-free `f` whose executable Berlekamp factorization returns
at most one factor, `f` is irreducible. Composes the structural loop lemma
`kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one` with the
algebraic completeness theorem
`irreducible_of_no_kernelWitnessSplit_squareFree`.
-/
theorem berlekampFactor_singleton_irreducible
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : ∀ d, d ∣ f → d ∣ DensePoly.derivative f →
      isUnitPolynomial d = true)
    (hsmall : (berlekampFactor f hmonic).factors.length ≤ 1) :
    FpPoly.Irreducible f :=
  irreducible_of_no_kernelWitnessSplit_squareFree
    f hmonic hsquareFree
    (kernelWitnessSplit?_none_of_berlekampFactor_factors_length_le_one
      f hmonic hsmall)

/--
The executable Berlekamp factor list of a square-free monic input has no
duplicates.  Composes the abstract loop invariant
`Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared`
(`HexBerlekamp/Factor.lean`) with the squareness-implies-`isUnitPolynomial`
result `Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd`.
-/
theorem berlekampFactor_factors_nodup
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hsquareFree : DensePoly.gcd f (DensePoly.derivative f) = 1) :
    (berlekampFactor f hmonic).factors.Nodup := by
  apply berlekampFactor_factors_nodup_of_no_squared
  intro g hgg hpos
  have hunit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_squareFree_of_squared_dvd
      (squareFree_common_of_gcd_eq_one hsquareFree) hgg
  have hdeg : g.degree? = some 0 := by
    unfold isUnitPolynomial at hunit
    cases hd : g.degree? with
    | none => rw [hd] at hunit; simp at hunit
    | some k =>
        rw [hd] at hunit
        cases k with
        | zero => rfl
        | succ _ => simp at hunit
  rw [hdeg] at hpos
  simp at hpos

end

end Berlekamp
end Hex
