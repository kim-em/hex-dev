/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekamp.Irreducibility
public import HexBerlekamp.Factor
public import HexPolyFp.Compose
public import HexPolyFp.Quotient
public import HexPolyFp.QuotientFrobenius
public import HexArith.Nat.Pow
public import HexBerlekamp.RabinSoundness.RabinCore
import all HexBerlekamp.RabinSoundness.RabinCore

public section
set_option backward.proofsInPublic true

/-!
The prime-field product identity and `xPowSubX 1` shape, the structural
lemmas, the `rabinTest_imp_irreducible` soundness theorem, and the
certificate-checker corollaries.
-/
namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
/-! ### Prime-field product identity -/

/-- Every prime-field residue is a root of `xPowSubX 1`: this is Fermat's
little theorem packaged through the executable `FpPoly` evaluation. -/
theorem xPowSubX_one_eval_eq_zero (c : ZMod64 p) :
    DensePoly.eval (xPowSubX (p := p) 1) c = 0 := by
  unfold xPowSubX
  rw [FpPoly.eval_sub, FpPoly.eval_monomial, FpPoly.eval_X,
    Nat.pow_one, ZMod64.pow_prime_of_prime_modulus]
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
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring, DensePoly.coeff_sub_ring]
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
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial, DensePoly.coeff_C]
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

/-- Multiplying two monic prime-field polynomials yields a monic polynomial. -/
private theorem monic_mul_monic (a b : FpPoly p)
    (ha_ne : a ≠ 0) (hb_ne : b ≠ 0)
    (ha : DensePoly.Monic a) (hb : DensePoly.Monic b) :
    DensePoly.Monic (a * b) := by
  unfold DensePoly.Monic
  unfold DensePoly.Monic at ha hb
  have hprod : DensePoly.leadingCoeff a * DensePoly.leadingCoeff b ≠ (0 : ZMod64 p) := by
    rw [ha, hb]
    grind
  have hlead := DensePoly.leadingCoeff_mul a b
    (FpPoly.size_pos_of_ne_zero ha_ne)
    (FpPoly.size_pos_of_ne_zero hb_ne)
    hprod
  change DensePoly.leadingCoeff (a * b) =
    DensePoly.leadingCoeff a * DensePoly.leadingCoeff b at hlead
  rw [hlead, ha, hb]
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
  have _hone_ne : (1 : FpPoly p) ≠ 0 := fpPoly_one_ne_zero
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
  rw [Nat.pow_one, DensePoly.coeff_sub_ring, DensePoly.coeff_monomial, DensePoly.coeff_monomial]
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
  rw [Nat.pow_one, DensePoly.coeff_sub_ring, DensePoly.coeff_monomial, DensePoly.coeff_monomial]
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
    exact FpPoly.leadingCoeff_mul a q ha_ne hq_ne
  have hq_lead : DensePoly.leadingCoeff q = q.coeff 0 := by
    rw [DensePoly.leadingCoeff_eq_coeff_last _ hq_pos, hq_size_one]
  have hq_coeff0 : q.coeff 0 = 1 := by
    unfold DensePoly.Monic at ha_monic hb_monic
    rw [ha_monic, hq_lead, hb_monic] at hlead_eq
    have : (1 : ZMod64 p) = 1 * q.coeff 0 := hlead_eq
    grind
  rw [hq, hq_eq_C, hq_coeff0]
  show a = a * (DensePoly.C (1 : ZMod64 p))
  rw [show (DensePoly.C (1 : ZMod64 p) : FpPoly p) = 1 from rfl, FpPoly.mul_one]

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
    rw [show (FpPoly.X : FpPoly p) = DensePoly.monomial 1 (1 : ZMod64 p) from rfl,
      FpPoly.linearPow_monomial_one]
    congr 1
    exact Nat.pow_one p
  rw [hxPow]
  exact FpPoly.compose_linearPow_X_sub_X w p

/-- Substituting an arbitrary witness into the prime-field product identity. -/
theorem primeFieldProduct_witness_eq (w : FpPoly p) :
    (ZMod64.values p).foldl
      (fun acc c => acc * (w - FpPoly.C c)) 1 =
        FpPoly.linearPow w p - w := by
  rw [← FpPoly.compose_primeFieldLinearProduct w, primeFieldProduct_X_eq_xPowSubX]
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


end Berlekamp
end Hex
