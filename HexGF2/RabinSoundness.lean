import HexGF2.Irreducibility

/-!
Project-side soundness bridge from `GF2Poly.rabinTest` to
`GF2Poly.Irreducible`.

The executable certificate checker in `HexGF2/Irreducibility.lean` already
proves soundness up to the Boolean `rabinTest` predicate. This module adds the
Rabin-theorem layer from `rabinTest = true` to the project-side packed
polynomial irreducibility predicate. The top-level proof is a contrapositive
Rabin argument; the finite-field algebra leaves are stated explicitly so they
can be discharged independently.
-/
namespace Hex
namespace GF2Poly

/-! ## Foundational Rabin leaves -/

/--
The absolute polynomial `X^(2^k) - X` in characteristic two.

Packed `GF(2)` subtraction is addition, so this is represented as
`X^(2^k) + X`.
-/
def xPowSubX (k : Nat) : GF2Poly :=
  monomial (2 ^ k) + monomial 1

/--
The executable Frobenius remainder vanishes exactly when `f` divides the
absolute Rabin polynomial `X^(2^k) - X`.

This is the GF2 counterpart of the absolute-to-modular bridge used by the
generic Berlekamp Rabin soundness proof.
-/
theorem dvd_xPowSubX_iff_frobeniusDiffMod_isZero
    (f : GF2Poly) (k : Nat) :
    f ∣ xPowSubX k ↔ (frobeniusDiffMod f k).isZero = true := by
  sorry

/--
Every nonconstant factor of a packed GF2 polynomial has an irreducible factor.

The proof is the usual descent on degree, specialized to the project-side
`GF2Poly.Irreducible` predicate and the packed divisibility relation.
-/
theorem exists_irreducible_factor_of_factor
    {f a b : GF2Poly} (hab : a * b = f) (ha_pos : 0 < a.degree) :
    ∃ g : GF2Poly,
      GF2Poly.Irreducible g ∧ g ∣ a ∧
        0 < g.degree ∧ g.degree ≤ a.degree := by
  sorry

/--
Forward Rabin degree theorem for packed GF2 polynomials.

If an irreducible `g` of positive degree divides `X^(2^n) - X`, then
`deg g` divides `n`.
-/
theorem degree_dvd_of_irreducible_dvd_xPowSubX
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) {n : Nat}
    (_hg_dvd : g ∣ xPowSubX n) :
    g.degree ∣ n := by
  sorry

/--
Backward Rabin degree theorem for packed GF2 polynomials.

An irreducible `g` of degree `d > 0` divides `X^(2^d) - X`.
-/
theorem irreducible_dvd_xPowSubX_degree
    {g : GF2Poly} (hg_irr : GF2Poly.Irreducible g)
    (hg_pos : 0 < g.degree) :
    g ∣ xPowSubX g.degree := by
  sorry

private theorem mulXk_zero' (p : GF2Poly) : p.mulXk 0 = p := by
  apply ext_coeff
  intro n
  rw [coeff_mulXk, coeff_shiftLeft]
  simp [coeff]

private theorem one_mul' (p : GF2Poly) : (1 : GF2Poly) * p = p := by
  show monomial 0 * p = p
  rw [monomial_mul, mulXk_zero']

private theorem mul_one' (p : GF2Poly) : p * (1 : GF2Poly) = p := by
  rw [mul_comm, one_mul']

private theorem dvd_refl' (p : GF2Poly) : p ∣ p :=
  ⟨1, (mul_one' p).symm⟩

private theorem dvd_zero' (p : GF2Poly) : p ∣ 0 :=
  ⟨0, (mul_zero p).symm⟩

private theorem dvd_add' {d a b : GF2Poly} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a + b := by
  rcases hda with ⟨ra, hra⟩
  rcases hdb with ⟨rb, hrb⟩
  exact ⟨ra + rb, by rw [hra, hrb, right_distrib]⟩

private theorem dvd_mul_left' {d a : GF2Poly} (c : GF2Poly) (hda : d ∣ a) :
    d ∣ c * a := by
  rcases hda with ⟨r, hr⟩
  refine ⟨c * r, ?_⟩
  rw [hr, ← mul_assoc, ← mul_assoc, mul_comm c d]

private theorem mul_dvd_mul_left' (c : GF2Poly) {a b : GF2Poly} (h : a ∣ b) :
    c * a ∣ c * b := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, by rw [hr, mul_assoc]⟩

/--
Geometric-series divisibility in characteristic two: `X^k + 1` divides
`X^(k*n) + 1` for any `k` and `n`.

Iterated XOR-cancellation gives the identity
`X^(k*(n+1)) + 1 = X^k * (X^(k*n) + 1) + (X^k + 1)`,
so the result reduces by induction on `n` to the base cases `n = 0`
(both sides are zero) and `n = 1` (reflexivity).
-/
private theorem monomial_add_one_dvd_geom (k : Nat) :
    ∀ n, (monomial k + 1) ∣ (monomial (k * n) + 1)
  | 0 => by
      rw [Nat.mul_zero, show (monomial 0 : GF2Poly) = 1 from rfl, add_self]
      exact dvd_zero' _
  | n + 1 => by
      have ih := monomial_add_one_dvd_geom k n
      have heq :
          monomial (k * (n + 1)) + 1 =
            monomial k * (monomial (k * n) + 1) + (monomial k + 1) := by
        rw [right_distrib, mul_one', monomial_mul_monomial]
        rw [show k + k * n = k * (n + 1) from by rw [Nat.mul_succ]; omega]
        rw [add_assoc]
        congr 1
        rw [← add_assoc, add_self, zero_add]
      rw [heq]
      exact dvd_add' (dvd_mul_left' (monomial k) ih) (dvd_refl' _)

/--
Number-theoretic companion to `monomial_add_one_dvd_geom`: when `d ∣ m`,
the integer `2 ^ d - 1` divides `2 ^ m - 1`.

Both follow from the same telescoping identity, transposed between the
polynomial and natural-number rings.
-/
private theorem two_pow_sub_one_dvd_two_pow_sub_one_of_dvd
    {d m : Nat} (hdvd : d ∣ m) : (2 ^ d - 1) ∣ (2 ^ m - 1) := by
  obtain ⟨k, rfl⟩ := hdvd
  induction k with
  | zero => simp
  | succ k ih =>
      have h2dk_pos : 0 < 2 ^ (d * k) := Nat.two_pow_pos _
      have h2d_pos : 0 < 2 ^ d := Nat.two_pow_pos _
      have hexp : 2 ^ (d * (k + 1)) = 2 ^ d * 2 ^ (d * k) := by
        rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
      have hge : 2 ^ d ≤ 2 ^ d * 2 ^ (d * k) := by
        calc 2 ^ d = 2 ^ d * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ d * 2 ^ (d * k) := Nat.mul_le_mul_left _ h2dk_pos
      have hkey :
          2 ^ (d * (k + 1)) - 1 = 2 ^ d * (2 ^ (d * k) - 1) + (2 ^ d - 1) := by
        rw [hexp, Nat.mul_sub, Nat.mul_one]
        omega
      rw [hkey]
      exact Nat.dvd_add (Nat.dvd_mul_left_of_dvd ih _) (Nat.dvd_refl _)

/--
Factor `xPowSubX d = monomial 1 * (monomial (2 ^ d - 1) + 1)`.

In characteristic two this collapses `X^(2^d) + X = X * (X^(2^d - 1) + 1)`.
The factor is uniform in `d ≥ 0`: when `d = 0` both sides reduce to `0`.
-/
private theorem xPowSubX_factor (d : Nat) :
    xPowSubX d = monomial 1 * (monomial (2 ^ d - 1) + 1) := by
  unfold xPowSubX
  rw [right_distrib, mul_one', monomial_mul_monomial]
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos _
  rw [show 1 + (2 ^ d - 1) = 2 ^ d from by omega]

/--
Divisibility chain on Rabin polynomials: if `d ∣ m`, then
`X^(2^d) - X` divides `X^(2^m) - X`.
-/
theorem xPowSubX_dvd_of_dvd {d m : Nat} (hdvd : d ∣ m) :
    xPowSubX d ∣ xPowSubX m := by
  obtain ⟨n, hn⟩ :=
    two_pow_sub_one_dvd_two_pow_sub_one_of_dvd hdvd
  have hgeo : (monomial (2 ^ d - 1) + 1) ∣ (monomial (2 ^ m - 1) + 1) := by
    rw [hn]
    exact monomial_add_one_dvd_geom (2 ^ d - 1) n
  rw [xPowSubX_factor d, xPowSubX_factor m]
  exact mul_dvd_mul_left' (monomial 1) hgeo

private theorem lt_of_mem_properDivisors {n d : Nat}
    (hmem : d ∈ properDivisors n) : d < n := by
  unfold properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range,
    decide_eq_true_eq] at hmem
  rcases hmem with ⟨⟨k, hk, rfl⟩, _⟩
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
Every positive proper divisor of `n` is contained in a maximal proper divisor
of `n`.

This routes an irreducible factor degree to one of the gcd legs checked by
`rabinTest`.
-/
theorem exists_maximalProperDivisor_dvd
    {n d : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ m, m ∈ maximalProperDivisors n ∧ d ∣ m :=
  exists_maximalProperDivisor_dvd_aux n (n - d) d hd_pos hd_dvd hd_lt (Nat.le_refl _)

/--
A common divisor of `f` and the absolute Rabin polynomial also divides the
modular Frobenius remainder used by the executable test.
-/
theorem dvd_frobeniusDiffMod_of_dvd_dvd
    {f g : GF2Poly} (hg_dvd_f : g ∣ f) {k : Nat}
    (hg_dvd_pow : g ∣ xPowSubX k) :
    g ∣ frobeniusDiffMod f k := by
  sorry

/--
A divisor of a unit polynomial is a unit polynomial.

For packed GF2 this is a degree argument over the executable divisibility
relation.
-/
theorem isUnitPolynomial_of_dvd_isUnitPolynomial
    {g h : GF2Poly} (hgh : g ∣ h) (hh : isUnitPolynomial h = true) :
    isUnitPolynomial g = true := by
  have hh_deg? : h.degree? = some 0 := by
    unfold isUnitPolynomial at hh
    cases hdeg : h.degree? with
    | none => rw [hdeg] at hh; simp at hh
    | some k =>
        rw [hdeg] at hh
        cases k with
        | zero => rfl
        | succ _ => simp at hh
  have hh_ne_zero : h ≠ 0 := ne_zero_of_degree?_eq_some hh_deg?
  have hg_ne_zero : g ≠ 0 := by
    intro hg
    rcases hgh with ⟨r, hr⟩
    apply hh_ne_zero
    rw [hr, hg, zero_mul]
  have hh_deg : h.degree = 0 := degree_eq_of_degree?_eq_some hh_deg?
  have hgle : g.degree ≤ h.degree :=
    degree_le_of_dvd_nonzero hg_ne_zero hh_ne_zero hgh
  rw [hh_deg] at hgle
  have hg_deg_zero : g.degree = 0 := Nat.eq_zero_of_le_zero hgle
  have hg_isZero_false : g.isZero = false := by
    cases hzero : g.isZero
    · rfl
    · exact False.elim (hg_ne_zero (eq_zero_of_isZero hzero))
  obtain ⟨d, hd⟩ := degree?_isSome_of_isZero_false hg_isZero_false
  have hd0 : d = 0 := by simpa [degree, hd] using hg_deg_zero
  unfold isUnitPolynomial
  rw [hd, hd0]

/-! ## Small structural helpers -/

/-- Local divisibility transitivity for `GF2Poly`. -/
private theorem dvd_trans {a b c : GF2Poly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨r, hr⟩
  rcases hbc with ⟨s, hs⟩
  refine ⟨r * s, ?_⟩
  rw [hs, hr, mul_assoc]

/-- A polynomial of positive degree is nonzero. -/
theorem ne_zero_of_pos_degree {f : GF2Poly} (hpos : 0 < f.degree) : f ≠ 0 := by
  intro hzero
  rw [hzero] at hpos
  simp at hpos

/-- The left factor in a factorization of a nonzero polynomial is nonzero. -/
theorem factor_ne_zero_of_ne_zero
    {f a b : GF2Poly} (hab : a * b = f) (hf_ne_zero : f ≠ 0) :
    a ≠ 0 := by
  intro hzero
  rw [hzero, zero_mul] at hab
  exact hf_ne_zero hab.symm

/-- A nonzero polynomial whose degree is not zero has positive degree. -/
theorem pos_degree_of_ne_zero_of_not_degree_zero
    {a : GF2Poly} (_ha_ne_zero : a ≠ 0) (ha_not_unit : a.degree ≠ 0) :
    0 < a.degree := by
  omega

/-- A nonzero packed `GF2Poly` has a successful `degree?` computation. -/
private theorem degree?_isSome_of_ne_zero
    {p : GF2Poly} (hp : p ≠ 0) :
    ∃ d, p.degree? = some d := by
  apply degree?_isSome_of_isZero_false
  cases h : p.isZero with
  | true => exact (hp (eq_zero_of_isZero h)).elim
  | false => rfl

/--
The degree of a factor `a` is strictly less than the degree of `f` whenever
the cofactor `b` has positive degree.
-/
theorem factor_degree_lt
    {f a b : GF2Poly}
    (hab : a * b = f) (ha_ne_zero : a ≠ 0) (hb_pos : 0 < b.degree) :
    a.degree < f.degree := by
  have hb_ne_zero : b ≠ 0 := ne_zero_of_pos_degree hb_pos
  obtain ⟨da, hda⟩ := degree?_isSome_of_ne_zero ha_ne_zero
  obtain ⟨db, hdb⟩ := degree?_isSome_of_ne_zero hb_ne_zero
  have hab_deg : (a * b).degree? = some (da + db) :=
    degree?_mul_of_degree?_eq_some hda hdb
  have hf_deg : f.degree? = some (da + db) := hab ▸ hab_deg
  have ha_deg : a.degree = da := degree_eq_of_degree?_eq_some hda
  have hb_deg : b.degree = db := degree_eq_of_degree?_eq_some hdb
  have hf_deg_eq : f.degree = da + db := degree_eq_of_degree?_eq_some hf_deg
  rw [hb_deg] at hb_pos
  omega

/-- A positive-degree polynomial is not a unit polynomial. -/
theorem isUnitPolynomial_eq_false_of_pos_degree
    {g : GF2Poly} (hpos : 0 < g.degree) :
    isUnitPolynomial g = false := by
  unfold isUnitPolynomial
  cases hdeg : g.degree? with
  | none =>
      rfl
  | some k =>
      have hk : k = g.degree := by
        exact (degree_eq_of_degree?_eq_some hdeg).symm
      subst hk
      cases hcase : g.degree with
      | zero =>
          simp [hcase] at hpos
      | succ _ =>
          rfl

/--
The `m`-th maximal-proper-divisor witness of `rabinTest`: if the test passes,
the gcd leg holds at every maximal proper divisor.
-/
theorem rabinCoprimeTest_of_mem_maximalProperDivisors
    (f : GF2Poly)
    (hwitnesses : (rabinWitnesses f).all Prod.snd = true)
    {m : Nat} (hm : m ∈ maximalProperDivisors f.degree) :
    rabinCoprimeTest f m = true := by
  unfold rabinWitnesses at hwitnesses
  rw [List.all_eq_true] at hwitnesses
  have hmem :
      (m, rabinCoprimeTest f m) ∈
        (maximalProperDivisors f.degree).map
          (fun d => (d, rabinCoprimeTest f d)) :=
    List.mem_map.mpr ⟨m, hm, rfl⟩
  exact hwitnesses _ hmem

/--
If `gcd(f, q)` is a unit polynomial and `g` divides both `f` and `q`, then
`g` is itself a unit polynomial.
-/
theorem isUnitPolynomial_of_dvd_gcd_isUnit
    {f q g : GF2Poly}
    (hgf : g ∣ f) (hgq : g ∣ q)
    (hgcd : isUnitPolynomial (gcd f q) = true) :
  isUnitPolynomial g = true :=
  isUnitPolynomial_of_dvd_isUnitPolynomial
    (dvd_gcd g f q hgf hgq) hgcd

/-! ## Bridge theorem -/

/--
Soundness of the executable Rabin test against `GF2Poly.Irreducible`.

The proof decomposes the Boolean test, picks an irreducible factor of any
nontrivial factorization, routes its degree through a maximal proper divisor,
and contradicts the corresponding gcd leg.
-/
theorem rabinTest_imp_irreducible
    (f : GF2Poly) (hrabin : rabinTest f = true) :
    GF2Poly.Irreducible f := by
  simp only [rabinTest, Bool.and_eq_true, decide_eq_true_eq] at hrabin
  obtain ⟨⟨hpos, hdivides⟩, hwitnesses⟩ := hrabin
  have hdiff_isZero :
      (frobeniusDiffMod f f.degree).isZero = true := by
    unfold rabinDividesTest at hdivides
    exact hdivides
  have hf_dvd_xPowSubX_n : f ∣ xPowSubX f.degree :=
    (dvd_xPowSubX_iff_frobeniusDiffMod_isZero f f.degree).mpr hdiff_isZero
  have hf_ne_zero : f ≠ 0 := ne_zero_of_pos_degree hpos
  refine ⟨hf_ne_zero, ?_⟩
  intro a b hab
  by_cases ha_unit : a.degree = 0
  · exact Or.inl ha_unit
  refine Or.inr ?_
  by_cases hb_unit : b.degree = 0
  · exact hb_unit
  exfalso
  have ha_ne_zero : a ≠ 0 := factor_ne_zero_of_ne_zero hab hf_ne_zero
  have hb_ne_zero : b ≠ 0 := by
    have hba : b * a = f := by
      rw [mul_comm]
      exact hab
    exact factor_ne_zero_of_ne_zero hba hf_ne_zero
  have ha_pos : 0 < a.degree :=
    pos_degree_of_ne_zero_of_not_degree_zero ha_ne_zero ha_unit
  have hb_pos : 0 < b.degree :=
    pos_degree_of_ne_zero_of_not_degree_zero hb_ne_zero hb_unit
  have ha_lt : a.degree < f.degree :=
    factor_degree_lt hab ha_ne_zero hb_pos
  obtain ⟨g, hg_irr, hg_dvd_a, hg_deg_pos, hg_deg_le_a⟩ :=
    exists_irreducible_factor_of_factor hab ha_pos
  have hg_dvd_f : g ∣ f := by
    rcases hg_dvd_a with ⟨r, hr⟩
    refine ⟨r * b, ?_⟩
    calc
      f = a * b := hab.symm
      _ = (g * r) * b := by rw [hr]
      _ = g * (r * b) := by rw [mul_assoc]
  have hg_dvd_xPowSubX_n : g ∣ xPowSubX f.degree :=
    dvd_trans hg_dvd_f hf_dvd_xPowSubX_n
  have hdeg_dvd : g.degree ∣ f.degree :=
    degree_dvd_of_irreducible_dvd_xPowSubX hg_irr hg_deg_pos hg_dvd_xPowSubX_n
  have hdeg_lt : g.degree < f.degree :=
    Nat.lt_of_le_of_lt hg_deg_le_a ha_lt
  obtain ⟨m, hm_mem, hdeg_dvd_m⟩ :=
    exists_maximalProperDivisor_dvd hg_deg_pos hdeg_dvd hdeg_lt
  have hg_dvd_xPowSubX_deg : g ∣ xPowSubX g.degree :=
    irreducible_dvd_xPowSubX_degree hg_irr hg_deg_pos
  have hxPow_dvd_xPow : xPowSubX g.degree ∣ xPowSubX m :=
    xPowSubX_dvd_of_dvd hdeg_dvd_m
  have hg_dvd_xPowSubX_m : g ∣ xPowSubX m :=
    dvd_trans hg_dvd_xPowSubX_deg hxPow_dvd_xPow
  have hg_dvd_frob : g ∣ frobeniusDiffMod f m :=
    dvd_frobeniusDiffMod_of_dvd_dvd hg_dvd_f hg_dvd_xPowSubX_m
  have hcoprime : rabinCoprimeTest f m = true :=
    rabinCoprimeTest_of_mem_maximalProperDivisors f hwitnesses hm_mem
  have hgcd_unit : isUnitPolynomial (gcd f (frobeniusDiffMod f m)) = true := by
    unfold rabinCoprimeTest at hcoprime
    exact hcoprime
  have hg_unit : isUnitPolynomial g = true :=
    isUnitPolynomial_of_dvd_gcd_isUnit hg_dvd_f hg_dvd_frob hgcd_unit
  have hg_not_unit : isUnitPolynomial g = false :=
    isUnitPolynomial_eq_false_of_pos_degree hg_deg_pos
  rw [hg_not_unit] at hg_unit
  exact Bool.noConfusion hg_unit

/--
Accepted executable irreducibility certificates imply project-side
`GF2Poly.Irreducible`, composing checker soundness with Rabin soundness.
-/
theorem checkIrreducibilityCertificate_imp_irreducible
    (f : GF2Poly) (cert : IrreducibilityCertificate)
    (hcheck : checkIrreducibilityCertificate f cert = true) :
    GF2Poly.Irreducible f :=
  rabinTest_imp_irreducible f
    (checkIrreducibilityCertificate_rabinTest f cert hcheck)

end GF2Poly
end Hex
