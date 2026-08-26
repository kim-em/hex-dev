/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp

public section
set_option backward.proofsInPublic true

/-!
Monic linear factors over a prime field, root enumeration, and the
reconstruction of a completely split monic polynomial from its roots.

`primeFieldLinearFactor c` is `X - c`. The module collects what every consumer
of those factors needs: their degree and monicity, the pairwise coprimality of
distinct ones, and the two `foldl` invariants that a product of such factors
divides a polynomial they all divide and has size one more than the number of
factors.

`rootsIn f` enumerates the roots of `f` in `F_p` by scanning the canonical
residue list. When it finds `deg f` of them, `eq_foldl_rootsIn_of_length` shows
that the corresponding linear factors multiply back to `f`, so a monic `f` that
is completely split with distinct roots is recovered from its roots alone. This
is the algebraic content behind the root-extraction path of
`Hex.Berlekamp.berlekampFactor`; the Rabin-test machinery uses the same
linear-factor lemmas for the `X^p - X` product identity.
-/
namespace Hex
namespace Berlekamp

variable {p : Nat} [ZMod64.Bounds p]

/-! # Monic linear factors -/

/-- The linear factor corresponding to a prime-field residue. -/
@[expose]
def primeFieldLinearFactor (c : ZMod64 p) : FpPoly p :=
  FpPoly.X - FpPoly.C c

/-- The listed prime-field linear factors are genuinely degree-one candidates. -/
theorem primeFieldLinearFactor_coeff_one (c : ZMod64 p) :
    (primeFieldLinearFactor c).coeff 1 = (1 : ZMod64 p) := by
  unfold primeFieldLinearFactor FpPoly.X FpPoly.C
  rw [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial, DensePoly.coeff_C]
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
  exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hcoeff

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
theorem primeFieldLinearFactor_size [ZMod64.PrimeModulus p] (c : ZMod64 p) :
    (primeFieldLinearFactor c).size = 2 := by
  have h_coeff_1_ne : (primeFieldLinearFactor c).coeff 1 ≠ 0 := by
    rw [primeFieldLinearFactor_coeff_one c]
    exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p))
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
theorem primeFieldLinearFactor_monic [ZMod64.PrimeModulus p] (c : ZMod64 p) :
    DensePoly.Monic (primeFieldLinearFactor c) := by
  unfold DensePoly.Monic
  rw [DensePoly.leadingCoeff_eq_coeff_last _
    (by rw [primeFieldLinearFactor_size]; omega)]
  rw [primeFieldLinearFactor_size]
  exact primeFieldLinearFactor_coeff_one c

/-- Each prime-field linear factor has degree exactly one. -/
theorem primeFieldLinearFactor_degree [ZMod64.PrimeModulus p] (c : ZMod64 p) :
    (primeFieldLinearFactor c).degree?.getD 0 = 1 := by
  have hsize := primeFieldLinearFactor_size (p := p) c
  unfold DensePoly.degree?
  simp [hsize]

/-- Distinct residues give distinct linear factors. -/
theorem primeFieldLinearFactor_injective {c d : ZMod64 p}
    (h : primeFieldLinearFactor c = primeFieldLinearFactor d) : c = d := by
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
  unfold primeFieldLinearFactor FpPoly.X FpPoly.C at hcoeff
  simp only [DensePoly.coeff_sub_ring, DensePoly.coeff_monomial,
    DensePoly.coeff_C] at hcoeff
  simp at hcoeff
  grind

/-! # Coprimality of distinct linear factors -/

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
private theorem C_ne_zero_dvd_one [ZMod64.PrimeModulus p] {a : ZMod64 p}
    (ha : a ≠ 0) :
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

private theorem dvd_trans_local {a b c : FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, FpPoly.mul_assoc]

/-- Distinct prime-field linear factors are coprime: any common divisor is a unit. -/
theorem primeFieldLinearFactor_distinct_common_dvd_one
    [ZMod64.PrimeModulus p] {c d : ZMod64 p}
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

/-- Coprime factors that both divide `q` have their product dividing `q`. -/
private theorem mul_dvd_of_dvd_dvd_common
    [ZMod64.PrimeModulus p] {a b q : FpPoly p}
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

/-- If `a` is coprime with both `b` and `c`, it is coprime with `b * c`. -/
private theorem coprime_mul_of_coprime_both [ZMod64.PrimeModulus p] (a b c : FpPoly p)
    (h_ab : ∀ e : FpPoly p, e ∣ a → e ∣ b → e ∣ (1 : FpPoly p))
    (h_ac : ∀ e : FpPoly p, e ∣ a → e ∣ c → e ∣ (1 : FpPoly p)) :
    ∀ e : FpPoly p, e ∣ a → e ∣ b * c → e ∣ (1 : FpPoly p) := by
  intro e he_a he_bc
  have he_coprime_b : ∀ d : FpPoly p, d ∣ b → d ∣ e → d ∣ (1 : FpPoly p) :=
    fun d hdb hde => h_ab d (dvd_trans_local hde he_a) hdb
  have he_c : e ∣ c :=
    FpPoly.dvd_of_dvd_mul_of_common_dvd_one he_bc he_coprime_b
  exact h_ac e he_a he_c

/-! # The two `foldl` invariants -/

/-- Foldl-shape divisibility: if every linear factor in `xs` divides `f`,
the cumulative `(acc * ∏ (X - C cᵢ))` divides `f` as long as `acc` is coprime
with each new linear factor. -/
theorem foldl_primeFieldLinearFactor_dvd
    [ZMod64.PrimeModulus p] (f : FpPoly p) (xs : List (ZMod64 p)) :
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

/-- Multiplying two monic prime-field polynomials yields a monic polynomial. -/
private theorem monic_mul_monic [ZMod64.PrimeModulus p] (a b : FpPoly p)
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

/-- The constant polynomial `1` over a prime modulus is nonzero. -/
theorem fpPoly_one_ne_zero [ZMod64.PrimeModulus p] : (1 : FpPoly p) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
  change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
  rw [DensePoly.coeff_zero] at hcoeff
  have hone_coeff : (1 : FpPoly p).coeff 0 = (1 : ZMod64 p) := by
    change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (1 : ZMod64 p)
    rw [DensePoly.coeff_C]
    simp
  rw [hone_coeff] at hcoeff
  exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) hcoeff

/-- The constant polynomial `1` over a prime modulus has size `1`. -/
theorem fpPoly_one_size [ZMod64.PrimeModulus p] : (1 : FpPoly p).size = 1 := by
  have h_le : (1 : FpPoly p).size ≤ 1 := by
    change (DensePoly.C (1 : ZMod64 p) : FpPoly p).size ≤ 1
    exact DensePoly.size_C_le_one (1 : ZMod64 p)
  have h_ge : 1 ≤ (1 : FpPoly p).size := FpPoly.size_pos_of_ne_zero fpPoly_one_ne_zero
  omega

/-- The constant polynomial `1` over a prime modulus is monic. -/
theorem fpPoly_one_monic [ZMod64.PrimeModulus p] : DensePoly.Monic (1 : FpPoly p) := by
  unfold DensePoly.Monic
  have _hone_ne : (1 : FpPoly p) ≠ 0 := fpPoly_one_ne_zero
  simp

/-- Foldl induction: size grows by one for each linear factor multiplied in. -/
theorem foldl_size_and_monic [ZMod64.PrimeModulus p]
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

/-! # Root enumeration -/

/--
The roots of `f` among the residues `ofNat p k` for `k < n`, listed in
increasing `k` and consed onto `acc`.

Counting down and consing keeps the loop tail-recursive and allocates only the
roots it keeps, so the scan holds `deg f` residues rather than the whole of
`F_p`. Filtering `ZMod64.values p` instead would allocate `p` residues, and the
budget in `Hex.Berlekamp.rootScanBudget` only bounds the scan against the
kernel computation it replaces, not in the absolute.
-/
@[expose]
def rootsBelow (f : FpPoly p) : Nat → List (ZMod64 p) → List (ZMod64 p)
  | 0, acc => acc
  | n + 1, acc =>
      let c := ZMod64.ofNat p n
      rootsBelow f n (if DensePoly.evalImpl f c = 0 then c :: acc else acc)

/--
The roots of `f` in `F_p`, listed in canonical residue order.

One Horner evaluation per residue, so `p * f.size` modular multiplications.
Callers gate the scan on the field size; see
`Hex.Berlekamp.rootScanBudget`.
-/
@[expose]
def rootsIn (f : FpPoly p) : List (ZMod64 p) :=
  rootsBelow f p []

/-- The accumulating scan collects exactly the residues below its bound at which
`f` vanishes, in increasing order. -/
private theorem rootsBelow_eq (f : FpPoly p) (n : Nat) (acc : List (ZMod64 p)) :
    rootsBelow f n acc =
      (((List.range n).map fun k => ZMod64.ofNat p k).filter
        fun c => decide (DensePoly.evalImpl f c = 0)) ++ acc := by
  induction n generalizing acc with
  | zero => simp [rootsBelow]
  | succ n ih =>
      rw [rootsBelow, ih, List.range_succ, List.map_append, List.filter_append]
      simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
      by_cases h : DensePoly.evalImpl f (ZMod64.ofNat p n) = 0
      · simp [h]
      · simp [h]

/-- The scan enumerates exactly the vanishing residues of the canonical residue
list: the loop is the filter, without materializing the list. -/
theorem rootsIn_eq_filter (f : FpPoly p) :
    rootsIn f =
      (ZMod64.values p).filter fun c => decide (DensePoly.evalImpl f c = 0) := by
  unfold rootsIn ZMod64.values
  rw [rootsBelow_eq]
  simp

/-- Membership in `rootsIn` is exactly vanishing of the evaluation. -/
@[grind =] theorem mem_rootsIn_iff (f : FpPoly p) (c : ZMod64 p) :
    c ∈ rootsIn f ↔ DensePoly.eval f c = 0 := by
  rw [rootsIn_eq_filter, List.mem_filter, DensePoly.eval_eq_evalImpl]
  simp [ZMod64.mem_values c]

/-- The root list has no duplicates: it enumerates the duplicate-free residue
list. -/
theorem rootsIn_nodup (f : FpPoly p) : (rootsIn f).Nodup := by
  rw [rootsIn_eq_filter]
  exact ZMod64.values_nodup.filter _

private theorem nodup_map_of_injective {α β : Type _} {xs : List α} {g : α → β}
    (hxs : xs.Nodup) (hinj : ∀ a b, g a = g b → a = b) :
    (xs.map g).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.nodup_cons] at hxs ⊢
      refine ⟨?_, ih hxs.2⟩
      intro hmem
      rcases List.mem_map.mp hmem with ⟨y, hy, hxy⟩
      have hyx : y = x := hinj y x hxy
      exact hxs.1 (hyx ▸ hy)

/-- Distinct residues give a duplicate-free list of monic linear factors. -/
theorem nodup_map_primeFieldLinearFactor {xs : List (ZMod64 p)} (h : xs.Nodup) :
    (xs.map primeFieldLinearFactor).Nodup :=
  nodup_map_of_injective h (fun _ _ hab => primeFieldLinearFactor_injective hab)

/-- Every listed root contributes its monic linear factor as a divisor of `f`. -/
theorem primeFieldLinearFactor_dvd_of_mem_rootsIn
    {f : FpPoly p} {c : ZMod64 p} (hc : c ∈ rootsIn f) :
    primeFieldLinearFactor c ∣ f :=
  FpPoly.X_sub_C_dvd_of_eval_eq_zero f c ((mem_rootsIn_iff f c).mp hc)

/-! # Reconstruction from a complete root list -/

/-- A size-one monic polynomial is `1`. -/
private theorem eq_one_of_size_one_of_monic
    (q : FpPoly p) (hsize : q.size = 1) (hmonic : DensePoly.Monic q) :
    q = 1 := by
  have hlead : q.coeff 0 = (1 : ZMod64 p) := by
    have h := DensePoly.leadingCoeff_eq_coeff_last q (by omega)
    rw [hsize] at h
    rw [← h]
    exact DensePoly.leadingCoeff_eq_one_of_monic hmonic
  apply DensePoly.ext_coeff
  intro n
  have h0 : (Zero.zero : ZMod64 p) = 0 := rfl
  cases n with
  | zero =>
      rw [hlead]
      change (1 : ZMod64 p) = (DensePoly.C (1 : ZMod64 p) : FpPoly p).coeff 0
      rw [DensePoly.coeff_C]
      simp
  | succ n =>
      rw [DensePoly.coeff_eq_zero_of_size_le q (by omega)]
      change (0 : ZMod64 p) = (DensePoly.C (1 : ZMod64 p) : FpPoly p).coeff (n + 1)
      rw [DensePoly.coeff_C]
      simp [h0]

/-- A monic divisor of a monic polynomial of the same size is that polynomial. -/
theorem eq_of_dvd_of_monic_of_size_eq [ZMod64.PrimeModulus p]
    {a f : FpPoly p} (hdvd : a ∣ f)
    (ha : DensePoly.Monic a) (hf : DensePoly.Monic f)
    (hf_ne : f ≠ 0) (hsize : a.size = f.size) :
    a = f := by
  rcases hdvd with ⟨q, hq⟩
  have ha_ne : a ≠ 0 := by
    intro h0
    exact hf_ne (by rw [hq, h0, FpPoly.zero_mul])
  have hq_ne : q ≠ 0 := by
    intro h0
    exact hf_ne (by rw [hq, h0, FpPoly.mul_zero])
  have hsizes := FpPoly.size_mul_eq_add_sub_one a q ha_ne hq_ne
  rw [← hq] at hsizes
  have ha_pos : 0 < a.size := FpPoly.size_pos_of_ne_zero ha_ne
  have hq_pos : 0 < q.size := FpPoly.size_pos_of_ne_zero hq_ne
  have hq_size : q.size = 1 := by omega
  have hlead := FpPoly.leadingCoeff_mul a q ha_ne hq_ne
  rw [← hq] at hlead
  unfold DensePoly.Monic at ha hf
  rw [hf, ha] at hlead
  have hq_monic : DensePoly.Monic q := by
    unfold DensePoly.Monic
    grind
  rw [hq, eq_one_of_size_one_of_monic q hq_size hq_monic]
  exact (DensePoly.mul_one_right_poly a).symm

/--
**Reconstruction from roots.** When the residue scan finds `deg f` distinct
roots of a monic `f`, the corresponding monic linear factors multiply back to
`f`: their product divides `f` (pairwise coprime divisors), is monic, and has
the same size, so it is `f` itself.
-/
theorem eq_foldl_rootsIn_of_length [ZMod64.PrimeModulus p]
    (f : FpPoly p) (hmonic : DensePoly.Monic f)
    (hlen : (rootsIn f).length + 1 = f.size) :
    (rootsIn f).foldl (fun acc c => acc * primeFieldLinearFactor c) 1 = f := by
  have hf_ne : f ≠ 0 := by
    intro h0
    have hzero : (0 : FpPoly p).size = 0 := rfl
    rw [h0, hzero] at hlen
    omega
  have hdvd :
      (rootsIn f).foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1 ∣ f := by
    apply foldl_primeFieldLinearFactor_dvd f (rootsIn f) 1 (rootsIn_nodup f)
      ⟨f, (FpPoly.one_mul f).symm⟩
    · intro c hc
      exact primeFieldLinearFactor_dvd_of_mem_rootsIn hc
    · intro _ _ e he_acc _
      exact he_acc
  have hshape := foldl_size_and_monic (p := p) (rootsIn f) 1
    fpPoly_one_ne_zero fpPoly_one_monic
  have hsize :
      ((rootsIn f).foldl (fun acc c => acc * (FpPoly.X - FpPoly.C c)) 1).size
        = f.size := by
    rw [hshape.2.2, fpPoly_one_size]
    omega
  exact eq_of_dvd_of_monic_of_size_eq hdvd hshape.2.1 hmonic hf_ne hsize

end Berlekamp

end Hex
