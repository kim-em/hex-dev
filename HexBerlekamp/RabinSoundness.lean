import HexBerlekamp.Irreducibility
import HexPolyFp.Quotient
import HexPolyFp.QuotientFrobenius
import HexArith.Nat.Pow

/-!
Project-side soundness bridge from `Berlekamp.rabinTest` to
`FpPoly.Irreducible`.

The executable irreducibility surface in `HexBerlekamp/Irreducibility.lean`
gives a `Bool` predicate `rabinTest f hmonic` capturing the three legs of
Rabin's criterion phrased through `frobeniusXPowMod`. This module bridges
`rabinTest = true` to the project-side `FpPoly.Irreducible` predicate from
`HexPolyFp/Basic.lean`, without going through Mathlib.

The bridge proof reduces to a small set of foundational lemmas tracked as
their own follow-up issues; `rabinTest_imp_irreducible` only orchestrates
them in a single contrapositive argument.
-/

namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

section

variable [ZMod64.PrimeModulus p]

/--
The polynomial `X^(p^k) - X` viewed inside the executable `FpPoly p` model.

Used to phrase the absolute (not modular) divisibility leg `f ∣ X^(p^n) - X`
underlying Rabin's test.
-/
def xPowSubX (k : Nat) : FpPoly p :=
  DensePoly.monomial (p ^ k) (1 : ZMod64 p) - FpPoly.X

/-! ### Foundational lemmas

The following declarations are stated with proofs deferred to their own
follow-up issues. Every other declaration in this file is a small
orchestration step on top of them. -/

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

Bridges the absolute polynomial `xPowSubX k` to the modular Frobenius
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
      have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
      rw [DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub]
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
        have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
        rw [DensePoly.coeff_sub _ _ _ hzero_sub]
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
  -- Step 2: bridge the LHS to the executable representative.
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
    have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
    have hzero_add : ((0 : ZMod64 p) + 0) = 0 := by grind
    rw [DensePoly.coeff_sub _ _ _ hzero_sub,
        DensePoly.coeff_add _ _ _ hzero_add,
        DensePoly.coeff_sub _ _ _ hzero_sub,
        DensePoly.coeff_sub _ _ _ hzero_sub]
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
  have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
  rw [DensePoly.coeff_sub _ _ _ hzero_sub]
  rw [FpPoly.coeff_monomial_mul]
  rw [DensePoly.coeff_sub _ _ _ hzero_sub]
  rw [DensePoly.coeff_monomial, DensePoly.coeff_monomial, hcoeff_one]
  by_cases hn0 : n = 0
  · subst hn0
    have h0pow_ne : ¬ 0 = p ^ k := by omega
    simp [h0pow_ne]
    grind
  · have hn_not_lt : ¬ n < 1 := by omega
    simp [hn_not_lt]
    rw [DensePoly.coeff_monomial]
    simp only [Lean.Grind.Semiring.one_mul]
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
      have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
      rw [DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub,
          DensePoly.coeff_sub _ _ _ hzero_sub]
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
    have hzero_sub : ((0 : ZMod64 p) - 0) = 0 := by grind
    rw [DensePoly.coeff_sub _ _ _ hzero_sub,
        DensePoly.coeff_sub _ _ _ hzero_sub]
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

/-! ### Bridge theorem -/

/--
Soundness of the executable Rabin test against the project-side
`FpPoly.Irreducible` predicate.

The proof orchestrates the foundational lemmas above. The combinatorial
shape (decomposing `rabinTest`, picking a monic irreducible factor of
size strictly between `0` and `n`, routing through a maximal proper
divisor, and contradicting the gcd leg) lives here. The heavy
mathematical content (Rabin's degree theorem in both directions,
finite-field factor existence, the absolute–modular Frobenius bridge,
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
bridge above.
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

theorem isUnitPolynomial_of_squareFree_of_squared_dvd
    {r g : FpPoly p}
    (hsf : DensePoly.gcd r (DensePoly.derivative r) = 1)
    (hgg : g * g ∣ r) :
    isUnitPolynomial g = true := by
  have hgr : g ∣ r := by
    rcases hgg with ⟨b, hb⟩
    refine ⟨g * b, ?_⟩
    rw [hb]
    exact DensePoly.mul_assoc_poly g g b
  have hgr' : g ∣ DensePoly.derivative r := dvd_derivative_of_squared_dvd hgg
  have hg_dvd_one : g ∣ (1 : FpPoly p) := by
    rw [← hsf]
    exact DensePoly.dvd_gcd g r (DensePoly.derivative r) hgr hgr'
  exact isUnitPolynomial_of_dvd_isUnitPolynomial hg_dvd_one isUnitPolynomial_one_FpPoly

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
    (hsquareFree : DensePoly.gcd (a * b) (DensePoly.derivative (a * b)) = 1)
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
  exact isUnitPolynomial_of_squareFree_of_squared_dvd hsf hg2_dvd_r

end

end Berlekamp
end Hex
